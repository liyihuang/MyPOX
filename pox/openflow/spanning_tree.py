# Copyright 2012,2013 James McCauley
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at:
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Creates a spanning tree.

This component uses the discovery component to build a view of the network
topology, constructs a spanning tree, and then disables flooding on switch
ports that aren't on the tree by setting their NO_FLOOD bit.  The result
is that topologies with loops no longer turn your network into useless
hot packet soup.

This component is inspired by and roughly based on the description of
Glenn Gibb's spanning tree module for NOX:
  http://www.openflow.org/wk/index.php/Basic_Spanning_Tree

Note that this does not have much of a relationship to Spanning Tree
Protocol.  They have similar purposes, but this is a rather different way
of going about it.
"""

from pox.core import core
import pox.openflow.libopenflow_01 as of
from pox.lib.revent import *
from collections import defaultdict
from pox.openflow.discovery import Discovery
from pox.lib.util import dpidToStr
from pox.lib.recoco import Timer
import time
import networkx as nx
import itertools
import pox.lib.packet as pkt

log = core.getLogger()

all_switches_set = set()

node_to_be_down = {}

# Might be nice if we made this accessible on core...
# _adj = defaultdict(lambda:defaultdict(lambda:[]))

def _calc_spanning_tree():
  """
Calculates the actual spanning tree

Returns it as dictionary where the keys are DPID1, and the
values are tuples of (DPID2, port-num), where port-num
is the port on DPID1 connecting to DPID2.
"""

  def flip(link):
    return Discovery.Link(link.dpid2, link.port2, link.dpid1, link.port1, link.link_type,link.available)

  adj = defaultdict(lambda: defaultdict(lambda: []))
  switches = set()
  # Add all links and switches
  for l in generator_for_link('lldp'):
    adj[l.dpid1][l.dpid2].append(l)
    switches.add(l.dpid1)
    switches.add(l.dpid2)

  # Cull links -- we want a single symmetric link connecting nodes
  for s1 in switches:
    for s2 in switches:
      if s2 not in adj[s1]:
        continue
      if not isinstance(adj[s1][s2], list):
        continue
      assert s1 is not s2
      good = False
      for l in adj[s1][s2]:
        if flip(l) in core.openflow_discovery.adjacency:
          # This is a good one
          adj[s1][s2] = l.port1
          adj[s2][s1] = l.port2
          good = True
          break
      if not good:
        del adj[s1][s2]
        if s1 in adj[s2]:
          # Delete the other way too
          del adj[s2][s1]
  q = []
  more = set(switches)

  done = set()
  tree = defaultdict(set)
  while True:
    q = sorted(list(more)) + q
    more.clear()
    if len(q) == 0: break
    v = q.pop(False)
    if v in done: continue
    done.add(v)
    for w, p in adj[v].iteritems():
      if w in tree: continue
      more.add(w)
      tree[v].add((w, p))
      tree[w].add((v, adj[w][v]))
  if False:
    log.debug("*** SPANNING TREE ***")
    for sw, ports in tree.iteritems():
      # print " ", dpidToStr(sw), ":", sorted(list(ports))
      # print " ", sw, ":", [l[0] for l in sorted(list(ports))]
      log.debug((" %i : " % sw) + " ".join([str(l[0]) for l in
                                            sorted(list(ports))]))
    log.debug("*********************")
  return tree


# Keep a list of previous port states so that we can skip some port mods
# If other things mess with port states, these may not be correct.  We
# could also refer to Connection.ports, but those are not guaranteed to
# be up to date.
_prev = defaultdict(lambda: defaultdict(lambda: None))

# If True, we set ports down when a switch connects
_noflood_by_default = False

# If True, don't allow turning off flood bits until a complete discovery
# cycle should have completed (mostly makes sense with _noflood_by_default).
_hold_down = False


def _handle_ConnectionUp(event):
  # When a switch connects, forget about previous port states
  _prev[event.dpid].clear()

  if _noflood_by_default:
    con = event.connection
    log.debug("Disabling flooding for %i ports", len(con.ports))
    for p in con.ports.itervalues():
      if p.port_no >= of.OFPP_MAX: continue
      _prev[con.dpid][p.port_no] = False
      pm = of.ofp_port_mod(port_no=p.port_no,
                           hw_addr=p.hw_addr,
                           config=of.OFPPC_NO_FLOOD,
                           mask=of.OFPPC_NO_FLOOD)
      con.send(pm)
    _invalidate_ports(con.dpid)

  if _hold_down:
    t = Timer(core.openflow_discovery.send_cycle_time + 1, _update_tree,
              kw={'force_dpid': event.dpid})


def _handle_LinkEvent(event):
  if event.link.link_type is 'lldp':

    # When links change, update spanning tree
    (dp1, p1), (dp2, p2) = event.link.end
    if _prev[dp1][p1] is False:
      if _prev[dp2][p2] is False:
        # We're disabling this link; who cares if it's up or down?
        # log.debug("Ignoring link status for %s", event.link)
        return
    _update_tree()

  elif event.link.link_type is 'broadcast':
    update_sw_cloud_site_domain()


def _update_tree(force_dpid=None):
  """
Update spanning tree

force_dpid specifies a switch we want to update even if we are supposed
to be holding down changes.
"""

  # Get a spanning tree
  tree = _calc_spanning_tree()
  log.debug("Spanning tree updated")

  # Connections born before this time are old enough that a complete
  # discovery cycle should have completed (and, thus, all of their
  # links should have been discovered).
  enable_time = time.time() - core.openflow_discovery.send_cycle_time - 1

  # Now modify ports as needed
  try:
    change_count = 0
    for sw, ports in tree.iteritems():
      con = core.openflow.getConnection(sw)
      if con is None: continue  # Must have disconnected
      if con.connect_time is None: continue  # Not fully connected

      if _hold_down:
        if con.connect_time > enable_time:
          # Too young -- we should hold down changes.
          if force_dpid is not None and sw == force_dpid:
            # .. but we'll allow it anyway
            pass
          else:
            continue

      tree_ports = [p[1] for p in ports]
      for p in con.ports.itervalues():
        if p.port_no < of.OFPP_MAX:
          flood = p.port_no in tree_ports
          if not flood:
            if core.openflow_discovery.is_edge_port(sw, p.port_no) or \
                    core.openflow_discovery._is_broadcast_port(sw,p.port_no):
              flood = True
          if _prev[sw][p.port_no] is flood:
            # print sw,p.port_no,"skip","(",flood,")"
            continue  # Skip
          change_count += 1
          _prev[sw][p.port_no] = flood
          # print sw,p.port_no,flood
          # TODO: Check results
          pm = of.ofp_port_mod(port_no=p.port_no,
                               hw_addr=p.hw_addr,
                               config=0 if flood else of.OFPPC_NO_FLOOD,
                               mask=of.OFPPC_NO_FLOOD)
          con.send(pm)

          _invalidate_ports(con.dpid)
    if change_count:
      log.info("%i ports changed", change_count)
  except:
    _prev.clear()
    log.exception("Couldn't push spanning tree")


def _check_path(dpid1, dpid2):
  if dpid1 == dpid2:
    return True
  else:
    g = _graph_for_link('lldp')
    return nx.has_path(g, dpid1, dpid2) if all(i in g.nodes() for i in [dpid1, dpid2]) else log.info(
      'not all nodes in g')


def _get_openflow_domain():
  g = _graph_for_link('lldp')
  domain_sw_dpid_set = set()
  sw_lldp_set = set()
  of_domain_set = set()
  for x in nx.connected_components(g):
    sw_lldp_set.update(x)
    domain_sw_dpid_set.add(frozenset(x))

  for x in all_switches_set.difference(sw_lldp_set):
    domain_sw_dpid_set.add(frozenset([x]))

  for dpid_set in domain_sw_dpid_set:
    of_domain = Of_domain(dpid_set)
    of_domain_set.add(of_domain)

  return of_domain_set


def _clear_flow_for_all_sw():
  all_switches_set.clear()
  for link in generator_for_link():
    all_switches_set.update([link.dpid1, link.dpid2])
  for sw in all_switches_set:
    clear = of.ofp_flow_mod(command=of.OFPFC_DELETE)
    con = core.openflow.getConnection(sw)
    if con is None: continue
    con.send(clear)


def _clear_broadcast_link_availablity():
  for link in generator_for_link('broadcast'):
    link.available = True


def update_sw_cloud_site_domain():
  clouds_set, sites_set, switches_set = _set_switches_clouds_sites()

  _clear_flow_for_all_sw()
  _clear_broadcast_link_availablity()
  _set_port_status_for_every_site(switches_set)

  of_domain_sets = _get_openflow_domain()

  for domain in of_domain_sets:
    for site in sites_set:
      if site.sw_dpid_set.issubset(domain.sw_dpid_set):
        site.of_domain = domain
        domain.sites.add(site)
        continue

  sites_to_be_down = form_big_spanning_tree(clouds_set)
  if sites_to_be_down:
    switches_to_be_down = map(lambda x: x.switches[0], sites_to_be_down)
    global node_to_be_down
    node_to_be_down.clear()
    for x in switches_to_be_down:
      node_to_be_down[x.cloud.get_active_switches_for_cloud()] = x.dpid,x.port_number

     # map(lambda x: test[x.cloud.get_active_switches_for_cloud()] = (x.dpid,x.port_number),switches_to_be_down)
    _send_sw_flows_no_floods(switches_to_be_down)
    send_lldp_broadcast_drop_flow_for_switches(switches_to_be_down)




def form_big_spanning_tree(clouds):
  original_g = nx.Graph()

  if not clouds: return None
  for cloud in clouds:
    if not cloud.sites: return None
    for site in cloud.sites:
      if not site.switches: return None
      original_g.add_edge(cloud, site.of_domain,weight=site.switches[0].dpid, site=site)

  spt = nx.minimum_spanning_tree(original_g)
  spt_att = nx.get_edge_attributes(spt, 'site')
  original_g_att = nx.get_edge_attributes(original_g, 'site')

  return set(original_g_att.itervalues()) - set(spt_att.itervalues())


def _set_switches_clouds_sites():
  clouds_set = set()
  switches_set = set()
  sites_set = set()
  cloud_g = nx.Graph()

  for link in generator_for_link('broadcast'):
    cloud_g.add_edge(Switch(link.dpid1, link.port1), Switch(link.dpid2, link.port2))

  for clique in nx.find_cliques(cloud_g):
    cloud = Cloud()
    clouds_set.add(cloud)
    for sw in clique:
      sw.cloud = cloud
      cloud.switches.add(sw)
      switches_set.add(sw)

  for cloud in clouds_set:
    site_g = nx.Graph()
    for i in itertools.combinations_with_replacement(cloud.switches, 2):
      if _check_path(i[0].dpid, i[1].dpid):
        site_g.add_edge(i[0], i[1])

    for sw_in_site in nx.connected_components(site_g):
      sw_in_site.sort(key=lambda switch: switch.dpid)
      sw_in_site[0].active = True

      site = Site()
      sites_set.add(site)
      site.cloud = cloud
      cloud.sites.add(site)

      for sw in sw_in_site:
        sw.site = site
        site.add_switch(sw)

  return clouds_set, sites_set, switches_set


def _send_sw_flows_no_floods(switches_set):
  for sw in switches_set:
    con = core.openflow.getConnection(sw.dpid)

    if con is None:
      log.debug('There isnt any connection between %s and controller' % sw.dpid)
      continue
    if con.connect_time is None:
      log.debug('Not fully connected')
      continue


    pm = of.ofp_port_mod(port_no=sw.port_number, hw_addr=dpid_port_to_mac(sw.dpid, sw.port_number, con),
                         config=of.OFPPC_NO_FLOOD, mask=of.OFPPC_NO_FLOOD)
    con.send(pm)


def _set_port_status_for_every_site(switches_set):
  for switch in switches_set:
    con = core.openflow.getConnection(switch.dpid)

    if con is None:
      log.debug('There isnt any connection between %s and controller' % switch.dpid)
      continue
    if con.connect_time is None:
      log.debug('Not fully connected')
      continue
    if switch.active is False:
      send_lldp_broadcast_drop_flow (switch, con)
      _tag_broadcast_link(switch.dpid,switch.port_number)

    pm = of.ofp_port_mod(port_no=switch.port_number, hw_addr=dpid_port_to_mac(switch.dpid, switch.port_number, con),
                         config=0 if switch.active else of.OFPPC_NO_FLOOD, mask=of.OFPPC_NO_FLOOD)
    con.send(pm)


def send_lldp_broadcast_drop_flow_for_switches(switches):
  for sw in switches:
    con = core.openflow.getConnection(sw.dpid)
    if con is None or con.connect_time is None: pass
    send_lldp_broadcast_drop_flow(sw,con)


def send_lldp_broadcast_drop_flow(switch, con):
  if con is None or con.connect_time is None: return
  match_rule = defaultdict()
  match_rule['lldp'] = of.ofp_match(in_port=switch.port_number, dl_dst=pkt.ETHERNET.LLDP_MULTICAST,
                                    dl_type=pkt.ethernet.LLDP_TYPE)
  match_rule['broadcast'] = of.ofp_match(in_port=switch.port_number, dl_dst=pkt.ETHERNET.ETHER_BROADCAST,
                                         dl_type=pkt.ethernet.LLDP_TYPE)
  match_rule['any'] = of.ofp_match(in_port=switch.port_number)

  for key, match in match_rule.iteritems():
    add_flow_msg = of.ofp_flow_mod(match=match)
    if key is 'any':
      add_flow_msg.priority = of.OFP_DEFAULT_PRIORITY
      # add_flow_msg.actions.append(of.ofp_action_output(port=of.OFPP_NONE))
    else:
      add_flow_msg.priority = of.OFP_HIGH_PRIORITY
      add_flow_msg.actions.append(of.ofp_action_output(port=of.OFPP_CONTROLLER))

    con.send(add_flow_msg)


def dpid_port_to_mac(dpid, port_numer, con=None):
  if con is None:
    con = core.openflow.getConnection(dpid)
    if con is None: pass
    if con.connect_time is None: pass
  for port in con.original_ports._ports:
    if port_numer is port.port_no:
      return port.hw_addr


def generator_for_link(link_type=None):
  if link_type is None:
    return (l for l in core.openflow_discovery.adjacency)
  elif link_type is not 'lldp' and link_type is not 'broadcast':
    log.debug('type is not correct')
    return None
  else:
    return (l for l in core.openflow_discovery.adjacency if l.link_type is link_type)


_dirty_switches = {}  # A map dpid_with_dirty_ports->Timer
_coalesce_period = 2  # Seconds to wait between features requests


def _tag_broadcast_link(dpid,port_number):
  for link in generator_for_link('broadcast'):
    if ((dpid,port_number) == (link.dpid1,link.port1)) or ((dpid,port_number) == (link.dpid2, link.port2)):
      link.available = False


def _invalidate_ports(dpid):
  """
Registers the fact that port info for dpid may be out of date

When the spanning tree adjusts the port flags, the port config bits
we keep in the Connection become out of date.  We don't want to just
set them locally because an in-flight port status message could
overwrite them.  We also might not want to assume they get set the
way we want them.  SO, we do send a features request, but we wait a
moment before sending it so that we can potentially coalesce several.

TLDR: Port information for this switch may be out of date for around
    _coalesce_period seconds.
"""
  if dpid in _dirty_switches:
    # We're already planning to check
    return
  t = Timer(_coalesce_period, _check_ports, args=(dpid,))
  _dirty_switches[dpid] = t


def _check_ports(dpid):
  """
Sends a features request to the given dpid
"""
  _dirty_switches.pop(dpid, None)
  con = core.openflow.getConnection(dpid)
  if con is None: return
  con.send(of.ofp_barrier_request())
  con.send(of.ofp_features_request())
  log.debug("Requested switch features for %s", str(con))


class Switch(object):
  """docstring for switch"""

  def __init__(self, dpid=0, port_number=0, cloud=None, site=None, active=False):
    super(Switch, self).__init__()
    self.dpid = dpid
    self.port_number = port_number
    self.cloud = cloud
    self.site = site
    self.active = active

  def __str__(self):
    return 'dpid is %s, port_number is %s, the cloud is %s, the site is %s' % \
           (self.dpid, self.port_number, self.cloud, self.site)

  def __repr__(self):
    return 'dpid is %s, port_number is %s, the cloud is %s, the site is %s' % \
           (self.dpid, self.port_number, self.cloud, self.site)

  def __hash__(self):
    return self.dpid + self.port_number

  def __eq__(self, other):
    return self.dpid == other.dpid and self.port_number == other.port_number


class Cloud(object):
  def __init__(self):
    super(Cloud, self).__init__()
    self.switches = set()
    self.sites = set()

  def __repr__(self):
    return 'cloud ' + str([sw.dpid for sw in self.switches])

  def __str__(self):
    return 'cloud ' + str([sw.dpid for sw in self.switches])

  def get_active_switches_for_cloud(self):
    swithes = filter(lambda x: x.active is True,self.switches)
    return frozenset(map(lambda x: (x.dpid,x.port_number),swithes))


class Site(object, ):
  def __init__(self):
    super(Site, self).__init__()
    self.switches = []
    self.cloud = None
    self.sw_dpid_set = set()
    self.of_domain = None

  def add_switch(self, sw):
    self.switches.append(sw)
    self.sw_dpid_in_site()


  def sw_dpid_in_site(self):
    map(lambda sw: self.sw_dpid_set.add(sw.dpid), self.switches)
    return self.sw_dpid_set

  def __repr__(self):
    return 'site ' + str([sw.dpid for sw in self.switches])

  def __str__(self):
    return 'site ' + str([sw.dpid for sw in self.switches])


class Of_domain(object):
  def __init__(self, dpid_set=None):
    super(Of_domain, self).__init__()
    self.sw_dpid_set = dpid_set
    self.sites = set()

  def __repr__(self):
    return 'of_domain ' + str(self.sw_dpid_set)

  def __str__(self):
    return 'of_domain ' + str(self.sw_dpid_set)


def _graph_for_link(link_type):
  g = nx.Graph()
  for link in generator_for_link(link_type):
    g.add_edge(link.dpid1, link.dpid2)

  return g


def launch(no_flood=False, hold_down=False):
  global _noflood_by_default, _hold_down
  if no_flood is True:
    _noflood_by_default = True
  if hold_down is True:
    _hold_down = True

  def start_spanning_tree():
    core.openflow.addListenerByName("ConnectionUp", _handle_ConnectionUp)
    core.openflow_discovery.addListenerByName("LinkEvent", _handle_LinkEvent,priority=100)
    log.debug("Spanning tree component ready")

  core.call_when_ready(start_spanning_tree, "openflow_discovery")
