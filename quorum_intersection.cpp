/*
 * The MIT License
 *
 * Copyright (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 * associated documentation files (the "Software"), to deal in the Software without restriction,
 * including without limitation the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or
 * substantial
 * portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 * NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES
 * OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
 * IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */
#include <vector>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <algorithm>
#include <functional>
#include <random>

#include <boost/program_options.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/strong_components.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>
#include <boost/log/support/date_time.hpp>

#include <boost/log/core.hpp>
#include <boost/log/trivial.hpp>
#include <boost/log/expressions.hpp>


namespace logging = boost::log;
namespace po = boost::program_options;
using namespace std;
using namespace boost;

using NodeID = string;

struct QuorumSet {
  uint32_t threshold;
  vector<NodeID> nodeIds;
  vector<QuorumSet> innerSets;
};

struct StellarNode {
  NodeID node_id;
  string name;
  QuorumSet qSet;

  NodeID getId() {
    return node_id;
  }

  QuorumSet& getQuorumSet() {
    return qSet;
  }
};

template<typename T>
struct GenericQuorumSet {
  uint32_t threshold;
  vector<T> nodes;
  vector<GenericQuorumSet<T> > innerSets;
};

template<typename T, typename Q>
struct GenericStellarNode {
  T data;
  GenericQuorumSet<Q> qSet;
};

struct NodeData {
  NodeID nodeID;
  string name;
};

struct GraphQData;
using Graph3 = adjacency_list < vecS, vecS, directedS, GenericStellarNode<NodeData, GraphQData> >;
using NodeIx = Graph3::vertex_descriptor;

struct GraphQData {
  NodeIx index;
};

using Indexes = property_map<Graph3, vertex_index_t>::type;

bool containsQuorumSlice(NodeIx node,
                         const GenericQuorumSet<GraphQData>& quorumSet,
                         const vector<bool>& availableNodes,
                         const Indexes& indexes) {
  BOOST_LOG_TRIVIAL(trace) << endl << "checking a quorum slice for node " << node;
  if (!availableNodes[indexes[node]]) {
    BOOST_LOG_TRIVIAL(trace) << "no self";
    return false;
  }
  uint32_t threshold = quorumSet.threshold;
  uint32_t failLimit = static_cast<uint32_t>(quorumSet.nodes.size() +
                                             quorumSet.innerSets.size()) - threshold + 1;
  BOOST_LOG_TRIVIAL(trace) << "threshold: " << threshold;
  BOOST_LOG_TRIVIAL(trace) << "number of nodes to consider: "  << quorumSet.nodes.size();
  for (auto& id : quorumSet.nodes) {
    if (availableNodes[indexes[id.index]]) {
      threshold--;
      BOOST_LOG_TRIVIAL(trace) << "found a node from quorum slice. Its index: " << indexes[id.index];
    } else {
      failLimit--;
      BOOST_LOG_TRIVIAL(trace) << "missing " << id.index << " for " << node;
    }
    if (threshold == 0) {
      BOOST_LOG_TRIVIAL(trace) << "found quorum slice";
      return true;
    }
    if (failLimit == 0) {
      BOOST_LOG_TRIVIAL(trace) << "insufficient nodes";
      return false;
    }
  }
  for (auto& qSet : quorumSet.innerSets) {
    if (containsQuorumSlice(node, qSet, availableNodes, indexes)) {
      threshold--;
    } else {
      failLimit--;
      BOOST_LOG_TRIVIAL(trace) << "missing inner set for " << node;
    }
    if (threshold == 0) {
      BOOST_LOG_TRIVIAL(trace) << "found quorum slice";
      return true;
    }
    if (failLimit == 0) {
      BOOST_LOG_TRIVIAL(trace) << "insufficient nodes";
      return false;
    }
  }
  BOOST_LOG_TRIVIAL(trace) << "no quorum slice";
  return false;
}

vector<NodeIx> containsQuorum(vector<NodeIx> nodes,
                              vector<bool>& availableNodes,
                              const Graph3& graph,
                              const Indexes& indexes) {
  vector<NodeIx> removedNodes;
  vector<NodeIx> filtered;
  auto count = nodes.size();
  // searching for the greatest fix-point of f(X) = {x: x \in X such that x has a quorum slice in X}
  do {

    BOOST_LOG_TRIVIAL(trace) << endl << endl << endl
                             << "-----starting new round-----"
                             << endl << endl << endl;
    count = nodes.size();
    BOOST_LOG_TRIVIAL(trace) << "nodes size: " << count;
    filtered.clear();
    copy_if(nodes.begin(), nodes.end(), back_inserter(filtered), [&graph, &availableNodes, &indexes, &removedNodes](NodeIx node) {
        if (!containsQuorumSlice(node, graph[node].qSet, availableNodes, indexes)) {
          if (availableNodes[indexes[node]]) {
            availableNodes[indexes[node]] = false;
            removedNodes.push_back(node);
          }
          return false;
        }
        return true;
      });
    nodes = filtered;
    BOOST_LOG_TRIVIAL(trace) << "number of filtered nodes: " << nodes.size();

  } while (count != nodes.size());

  for (const NodeIx& node : removedNodes) {
    availableNodes[indexes[node]] = true;
  }

  BOOST_LOG_TRIVIAL(trace) << "quorum size: " << nodes.size();
  return nodes;
}

bool isMinimalQuorum(vector<NodeIx> nodes,
                     vector<bool> availableNodes,
                     const Graph3& graph,
                     const Indexes& indexes) {
  BOOST_LOG_TRIVIAL(trace) << "checking for minimal quorum, size: " << nodes.size();
  vector<NodeIx> nodesV(nodes.begin(), nodes.end());
  if (containsQuorum(nodesV, availableNodes, graph, indexes).empty()) {
    BOOST_LOG_TRIVIAL(trace) << "it does not contain a quorum";
    return false;
  }
  for (NodeIx node : nodes) {

    BOOST_LOG_TRIVIAL(trace) << "removing node from minimal candidate: " << node;
    auto index = indexes[node];
    BOOST_LOG_TRIVIAL(trace) << "its index: " << index << endl;
    availableNodes[index] = false;

    for (const auto& av : availableNodes) {
      BOOST_LOG_TRIVIAL(trace) << av << " ";
    }

    if (!containsQuorum(nodesV, availableNodes, graph, indexes).empty()) {
      BOOST_LOG_TRIVIAL(trace) << "found smaller quorum";
      return false;
    }

    availableNodes[index] = true;
  }
  BOOST_LOG_TRIVIAL(trace) << "is minimal";
  return true;
}

NodeIx findBestNode(const vector<NodeIx>& quorum,
                    const vector<NodeIx>& restriction,
                    const Graph3& graph,
                    const Indexes& indexes) {
  static default_random_engine generator{random_device{}()};

  // choose uniformly at random a node with max in degree
  vector<bool> availableNodes(num_vertices(graph), false);
  vector<uint64_t> inDegreeCount(num_vertices(graph), 0);
  for (const NodeIx& node : quorum) {
    availableNodes[indexes[node]] = true;
  }
  for (const NodeIx& node : restriction) {
    availableNodes[indexes[node]] = false;
  }

  auto& nodes = !restriction.empty() ? restriction : quorum;

  uint64_t maxValue = 0;
  int maxCount = 1;
  NodeIx bestNode = *quorum.begin();
  for (const NodeIx& node : quorum) {
    Graph3::adjacency_iterator v1, v2;
    for (tie(v1, v2) = adjacent_vertices(node, graph); v1 != v2; v1++) {
      BOOST_LOG_TRIVIAL(trace) << "adjacent node: " << indexes[node] << " --> " << indexes[*v1];
      if (!availableNodes[indexes[*v1]]) {
        continue;
      }
      uint64_t nodesDegree = ++inDegreeCount[indexes[*v1]];
      if (nodesDegree >= maxValue) {
        if (nodesDegree == maxValue) {
          maxCount += 1;
          auto result = uniform_int_distribution<int>{1, maxCount}(generator);
          BOOST_LOG_TRIVIAL(trace) << "generated number: " << result << " max: " << maxCount;
          if (result != 1) {
            BOOST_LOG_TRIVIAL(trace) << "not switching max node";
            continue;
          }
          BOOST_LOG_TRIVIAL(trace) << "switching max";
        } else {
          maxCount = 1;
        }
        BOOST_LOG_TRIVIAL(trace) << "updating best node: " << *v1 << " " << nodesDegree;
        maxValue = nodesDegree;
        bestNode = *v1;
      }
    }
  }
  return bestNode;
}

bool iterateMinimalQuorums(vector<NodeIx> toRemove,
                           vector<NodeIx> dontRemove,
                           const Indexes& indexes,
                           const Graph3& graph,
                           std::function<bool(const vector<NodeIx>&)> visitor,
                           std::function<bool(const vector<NodeIx>&)> currentVisitor) {
  static uint64_t counter = 0;
  BOOST_LOG_TRIVIAL(trace) << "iterateMinimalQuorums counter: " << ++counter;

  if (currentVisitor(dontRemove)) {
    BOOST_LOG_TRIVIAL(trace) << "exiting due to currentVisitor";
    return false;
  }

  if (toRemove.empty() && dontRemove.empty()) {
    BOOST_LOG_TRIVIAL(trace) << "nodes are empty";
    return false;
  }
  BOOST_LOG_TRIVIAL(trace) << "toRemove size: " << toRemove.size();
  BOOST_LOG_TRIVIAL(trace) << "dontRemove size: " << dontRemove.size();
  vector<bool> availableNodes(num_vertices(graph), false);
  vector<NodeIx> nodes;

  for (NodeIx node : dontRemove) {
    availableNodes[indexes[node]] = true;
    nodes.push_back(node);
  }

  BOOST_LOG_TRIVIAL(trace) << "available nodes:";
  for (const auto& av : availableNodes) {
    BOOST_LOG_TRIVIAL(trace) << av << " ";
  }
  BOOST_LOG_TRIVIAL(trace) << endl;

  BOOST_LOG_TRIVIAL(trace) << "checking if dontRemove contains some quorum";
  if (!containsQuorum(nodes, availableNodes, graph, indexes).empty()) {
    BOOST_LOG_TRIVIAL(trace) << "dontRemove contains some quorum";
    if (isMinimalQuorum(dontRemove, availableNodes, graph, indexes)) {
      BOOST_LOG_TRIVIAL(trace) << "found minimal quorum of size " << dontRemove.size();
      return visitor(dontRemove);
    }
    BOOST_LOG_TRIVIAL(trace) << "failed to find minimal";

    BOOST_LOG_TRIVIAL(trace) << "dontRemove contains a quorum, so it is not minimal";
    return false;
  }

  BOOST_LOG_TRIVIAL(trace) << "toRemove size: " << toRemove.size();
  for (NodeIx node : toRemove) {
    availableNodes[indexes[node]] = true;
    nodes.push_back(node);
    // BOOST_LOG_TRIVIAL(trace) << "abacd " << node << endl;
  }

  BOOST_LOG_TRIVIAL(trace) << "searching for any quorum, size: " << nodes.size() << " "
                           << toRemove.size() + dontRemove.size();
  for (const auto& av : availableNodes) {
    BOOST_LOG_TRIVIAL(trace) << av << " ";
  }
  BOOST_LOG_TRIVIAL(trace) << endl;
  auto quorum = containsQuorum(nodes, availableNodes, graph, indexes);
  BOOST_LOG_TRIVIAL(trace) << "searching for minimal quorums, max quorum size: " << quorum.size();
  if (quorum.empty()) {
    BOOST_LOG_TRIVIAL(trace) << "no available quorum";
    return false;
  }

  std::unordered_set<NodeIx> quorumNodes(quorum.begin(), quorum.end());
  for (NodeIx node : dontRemove) {
    if (quorumNodes.find(node) == quorumNodes.end()) {
      BOOST_LOG_TRIVIAL(trace) << "dontRemove not included";
      return false;
    }
  }

  // find best candidate to process next
  NodeIx bestNode = findBestNode(quorum, dontRemove, graph, indexes);

  BOOST_LOG_TRIVIAL(trace) << "best node: " << indexes[bestNode];

  for (NodeIx node : dontRemove) {
    quorumNodes.erase(node);
  }

  if (quorumNodes.empty()) {
    BOOST_LOG_TRIVIAL(trace) << "nothing left to check 2";
    return false;
  }

  // quorumNodes.erase(bestNode);
  toRemove.clear();
  copy_if(quorumNodes.begin(), quorumNodes.end(), back_inserter(toRemove),
          [&bestNode](const NodeIx& node) {
            return node != bestNode;
          });
  BOOST_LOG_TRIVIAL(trace) << "new toRemove size: " << quorumNodes.size();
  if (iterateMinimalQuorums(toRemove, dontRemove, indexes, graph, visitor, currentVisitor)) {
    BOOST_LOG_TRIVIAL(trace) << "recursive call returned true";
    return true;
  }

  BOOST_LOG_TRIVIAL(trace) << "first recursive call finished";

  dontRemove.push_back(bestNode);
  BOOST_LOG_TRIVIAL(trace) << "new dontRemove size: " << dontRemove.size();
  return iterateMinimalQuorums(toRemove, dontRemove, indexes, graph, visitor, currentVisitor);
}

QuorumSet parseQuorumSet(const property_tree::ptree& value) {
  using namespace boost::property_tree;

  QuorumSet result;
  if (value.empty()) {
    return result;
  }

  result.threshold = value.get<uint32_t>("threshold");
  for (const ptree::value_type& validator : value.get_child("validators")) {
    result.nodeIds.push_back(validator.second.get_value<string>());
  }
  for (const ptree::value_type& innerSet : value.get_child("innerQuorumSets")) {
    result.innerSets.push_back(parseQuorumSet(innerSet.second));
  }
  return result;
}

vector<StellarNode> parseStellarConfigurationJSON(istream& is) {
  vector<StellarNode> result;

  using namespace boost::property_tree;
  ptree root;
  read_json(is, root);

  for (ptree::value_type& node : root) {
    NodeID publicKey = node.second.get<NodeID>("publicKey");
    string name = node.second.get<string>("name");
    QuorumSet qSet = parseQuorumSet(node.second.get_child("quorumSet"));
    StellarNode stellarNode{publicKey, name, qSet};
    result.push_back(stellarNode);
  }

  return result;
}

Graph3 buildDependencyGraph3(const vector<StellarNode>& nodes) {
  Graph3 result;
  std::unordered_map<NodeID, NodeIx> idMap;
  for (auto& node : nodes) {
    auto newNode = GenericStellarNode<NodeData, GraphQData>{NodeData{ node.node_id, node.name },
                                                            GenericQuorumSet<GraphQData>{}};
    auto v = add_vertex(newNode, result);
    idMap[node.node_id] = v;
  }

  std::function<void(Graph3::vertex_descriptor,
                     GenericQuorumSet<GraphQData>&, const QuorumSet&)> addEdges;
  addEdges = [&result, &addEdges, &idMap]
    (Graph3::vertex_descriptor nodeIx,
     GenericQuorumSet<GraphQData>& quorumSet,
     const QuorumSet& orig) {
    quorumSet.threshold = orig.threshold;
    for (auto& trust : orig.nodeIds) {
      auto v = idMap[trust];
      quorumSet.nodes.push_back(GraphQData{v});
      add_edge(nodeIx, v, result);
    }

    for (const auto& innerSet : orig.innerSets) {
      quorumSet.innerSets.push_back({});
      addEdges(nodeIx, quorumSet.innerSets.back(), innerSet);
    }
  };

  for (auto& node : nodes) {
    auto& nodeIx = idMap[node.node_id];
    addEdges(nodeIx, result[nodeIx].qSet, node.qSet);
  }

  return result;
}

template<typename T>
void printQuorum(const vector<NodeIx>& quorum, const Graph3& graph, T& out) {
  // out << "Quorum:" << endl;
  for (auto& node : quorum) {
    auto& value = graph[node];
    out << value.data.name << " ";
    out << value.data.nodeID << endl;
    out << "( quorumslice: ";
    out << "threshold = " << value.qSet.threshold << " ";
    for (auto& nodeID : value.qSet.nodes) {
      auto& value2 = graph[nodeID.index];
      out << value2.data.nodeID << " ";
    }
    out << ") " << endl;
    out << endl;
  }
  out << endl;
}

template <typename Graph>
class NodeWriter {
public:
  NodeWriter(const Indexes& _indexes, const vector< uint >& _colors, uint _colorsCount, const Graph& _graph) :
    indexes(_indexes),
    colors(_colors),
    offset(0xFFFFFF / _colorsCount),
    graph(_graph) {
  }

  template <typename Vertex>
  void operator()(std::ostream& out, const Vertex& v) const {
    stringstream stream;
    stream << setfill ('0') << setw(3*2) << hex << offset * colors[indexes[v]];
    string color = stream.str();
    string label = graph[v].data.name.empty() ? graph[v].data.nodeID : graph[v].data.name;

    out << "[style=filled color=\"#" << color << "\" label=\"" << label << "\" fontcolor=\"white\"]";
  }
private:
  const Indexes& indexes;
  const Graph& graph;
  const vector< uint > colors;
  uint offset;
};

template<typename Graph>
void printGraphvizWithSccs(const Graph& graph,
                           ostream& out,
                           const vector< vector<NodeIx> >& sccs,
                           const Indexes& indexes) {
  vector< uint > colors(num_vertices(graph));
  for (auto it = 0u; it < sccs.size(); it++) {
    for (const auto& v : sccs[it]) {
      colors[indexes[v]] = it;
    }
  }
  write_graphviz(out, graph, NodeWriter<Graph>(indexes, colors, sccs.size(), graph));
  // boost::dynamic_properties dp;
  // dp.property("label", boost::get(&StellarNode::name, graph));
  // dp.property("label", boost::get(&GenericStellarNode<NodeData, GraphQData>::data::name, graph));
  // auto colorGetter = [&colors, &indexes](const NodeIx& node) -> int {
  //    return colors[indexes[node]];
  // };
  // dp.property("color", &colorGetter);
  // dp.property("color", );
  // dp.property("node_id", indexes);
  // write_graphviz_dp(out, graph, dp);
}

bool checkMinimalQuorums(const vector<NodeIx>& scc,
                         const Graph3& graph,
                         const Indexes& verIndexes,
                         vector<NodeIx>& foundQuorum1,
                         vector<NodeIx>& foundQuorum2) {
  bool result = true;
  vector<bool> availableNodes(num_vertices(graph), true);
  auto counter = 0;
  std::function< bool( const vector<NodeIx>& ) > visitor;
  visitor = [&result, &availableNodes, &scc, &graph, &verIndexes, &counter, &foundQuorum1, &foundQuorum2] (const vector<NodeIx>& quorum) -> bool {

    counter++;
    BOOST_LOG_TRIVIAL(trace) << "number of checked minimal quorums: " << counter;

    for (const auto& node : quorum) {
      availableNodes[verIndexes[node]] = false;
    }

    auto disjointQuorum = containsQuorum(scc, availableNodes, graph, verIndexes);
    if (!disjointQuorum.empty()) {
      result = false;

      foundQuorum1 = disjointQuorum;
      foundQuorum2 = vector<NodeIx>(quorum.begin(), quorum.end());
      BOOST_LOG_TRIVIAL(trace) << "sizes of disjoint quorums: "
                               << quorum.size() << " ,"
                               << disjointQuorum.size();
      return true;
    }

    for (const auto& node : quorum) {
      availableNodes[verIndexes[node]] = true;
    }
    return false;
  };

  std::function<bool(const vector<NodeIx>&)> currentVisitor;
  currentVisitor = [&scc](const vector<NodeIx>& qCandidate) -> bool {
    return qCandidate.size() > ((scc.size() / 2) + 1);
  };

  iterateMinimalQuorums(scc,
                        vector<NodeIx>(),
                        verIndexes,
                        graph,
                        visitor,
                        currentVisitor);
  return result;
}

bool solve(const Graph3& graph, ostream& cout, bool verbose, bool printGraphviz) {
  BOOST_LOG_TRIVIAL(trace) << "number of nodes: " << num_vertices(graph);

  // find all strongly connected components
  // all minimal quorums are inside of some scc
  vector<Graph3::vertices_size_type> components(num_vertices(graph));
  auto sccCount = strong_components
    (graph, make_iterator_property_map(components.begin(), get(vertex_index, graph)));

  // group nodes by their strongly connected components
  vector< vector<NodeIx> > sccs(sccCount);
  Graph3::vertex_iterator v1, v2;
  auto indexes = get(vertex_index, graph);
  for (tie(v1, v2) = vertices(graph); v1 != v2; v1++) {
    auto index = indexes[*v1];
    assert(index < components.size());
    assert(components[index] < sccs.size());
    sccs[components[index]].push_back(*v1);
  }

  if (printGraphviz) {
    printGraphvizWithSccs(graph, cout, sccs, indexes);
    return true;
  }

  if (verbose) {
    cout << "total number of strongly connected components: " << sccCount << endl;
  }

  // verify that all minimal quorums are contained only in the last (in topological order) strongly
  // connected component
  uint64_t nonIntersectingQs = 0;
  uint64_t count = 0;
  vector<bool> availableNodes(num_vertices(graph), false);
  vector<NodeIx> nodes;
  for (const auto& sComponent : sccs) {
    BOOST_LOG_TRIVIAL(trace) << endl << "checking Component #" << count++;

    nodes.clear();
    for (auto nodeIx : sComponent) {
      availableNodes[indexes[nodeIx]] = true;
      nodes.push_back(nodeIx);
    }

    auto quorum = containsQuorum(nodes, availableNodes, graph, indexes);
    if (!quorum.empty()) {
      nonIntersectingQs++;
      if (verbose) {
        cout << "found quorum inside of a strongly connected component:" << endl;
        printQuorum(quorum, graph, cout);
      }
    } else {
      BOOST_LOG_TRIVIAL(trace) << "no quorum inside of a strongly connected component";
    }

    for (const auto& nodeIx : sComponent) {
      availableNodes[indexes[nodeIx]] = false;
    }
  }
  if (verbose) {
    cout << "number of strongly connected components containing some quorum: " << nonIntersectingQs << endl;
    cout << "size of the main strongly connected component: " << sccs.front().size() << endl;
    cout << "main strongly connected component (all minimal quorums are included in it; "
		 << "small size means small resilience of the network):" << endl;
    printQuorum(sccs.front(), graph, cout);
  }

  if (nonIntersectingQs != 1) {
    if (verbose) {
      cout << "network's configuration is broken - more than one strongly connected component contains a quorum - "
           << nonIntersectingQs;
    }
    return false;
  }

  vector<NodeIx> q1, q2;
  if (!checkMinimalQuorums(sccs.front(), graph, indexes, q1, q2)) {
    if (verbose) {
      cout << "found two non-intersecting quorums" << endl;
      cout << "first quorum:" << endl;
      printQuorum(q1, graph, cout);
      cout << "second quorum:" << endl;
      printQuorum(q2, graph, cout);
    }
    return false;
  }

  if (verbose) {
    cout << "all quorums are intersecting" << endl;
  }
  return true;
}

bool solve(istream& cin, ostream& cout, bool verbose, bool printGraphviz) {
  Graph3 graph;
  {
    auto nodes = parseStellarConfigurationJSON(cin);
    graph = buildDependencyGraph3(nodes);
  }
  return solve(graph, cout, verbose, printGraphviz);
}

void initLogging(bool trace)
{
  if (trace) {
    logging::core::get()->set_filter(logging::trivial::severity >= logging::trivial::trace);
  } else {
    logging::core::get()->set_filter(logging::trivial::severity >= logging::trivial::info);
  }
}

int main(int argc, char* argv[])
{
  bool help = false;
  bool verbose = false;
  bool printGraphviz = false;
  bool trace = false;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("help,h", po::bool_switch(&help), "print usage message")
    ("verbose,v", po::bool_switch(&verbose), "print more details")
    ("graph,g", po::bool_switch(&printGraphviz), "print graphviz representation of network's configuration")
    ("trace,t", po::bool_switch(&trace), "enable tracing messages")
    ;

  try {
    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);
  } catch(boost::exception& e) {
    cout << "Invalid option!" << endl;
    cout << desc;
    return EXIT_FAILURE;
  }

  initLogging(trace);

  if (help) {
    cout << desc << endl;
    return EXIT_SUCCESS;
  }

  cout << boolalpha;
  bool result = solve(cin, cout, verbose, printGraphviz);
  if (result) {
    cout << true << endl;
  } else {
    cout << false << endl;
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
