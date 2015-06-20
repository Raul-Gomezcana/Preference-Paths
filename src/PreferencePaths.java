import java.io.IOException;
import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;

import org.neo4j.graphalgo.GraphAlgoFactory;
import org.neo4j.graphalgo.PathFinder;
import org.neo4j.graphdb.Direction;
import org.neo4j.graphdb.GraphDatabaseService;
import org.neo4j.graphdb.Node;
import org.neo4j.graphdb.Path;
import org.neo4j.graphdb.PathExpanders;
import org.neo4j.graphdb.Relationship;
import org.neo4j.graphdb.RelationshipType;
import org.neo4j.graphdb.Result;
import org.neo4j.graphdb.Transaction;
import org.neo4j.graphdb.factory.GraphDatabaseFactory;

import edu.sdsc.scigraph.internal.reachability.ReachabilityIndex;


public class PreferencePaths
{
    private static final String DB_PATH = "target/social4.db";
    //private static final String DB_PATH = "target/socialDouble.db";
    //private static final String DB_PATH = "target/socialQuad.db";
    
    private static final boolean PRIORITY_QUEUE = true;
    private static final boolean REACHABILITY_INDEX = false;
    private static final int MAX_HOPS = 15;
    private static final int TIME_OUT = 900000;
   
    private static final int LOWER_BOUND = 0;
    private static final int UPPER_BOUND = 1;
    private static final int NEGATIVE_REWARD = -1000000;
    private static final int INITIAL_LOWER_BOUND = 2000000;
    private static final int INITIAL_UPPER_BOUND = -1;
    
    private static GraphDatabaseService graphDb;
    private static ReachabilityIndex index;
    private Transaction tx;
    
    private HashMap<Node, Integer> lbMap;
    private HashMap<Node, Integer> ubMap;
    private HashMap<Node, Relationship[]> succMap;
    private HashMap<String, Integer> prefRewards;
    private HashMap<ArrayList<Relationship>, int[]> pathCosts;
    private int numPrefs;
    
    private static enum RelTypes implements RelationshipType
    {
        Temp
    }

    public void preferencePathQuery(String startNodesQuery, String endNodesQuery, ArrayList<String> preferenceQueries, ArrayList<String> excludeQueries) 
    {
        tx = graphDb.beginTx();
        this.index = index;
        // Get starting and ending nodes
        ArrayList<Long> sourceIds = getIdsQuery(startNodesQuery);
        ArrayList<Long> destinationIds = getIdsQuery(endNodesQuery);
        
        // Queries to get the preferences nodes and store reward in hash map
        prefRewards = new HashMap<String, Integer>();
        numPrefs = preferenceQueries.size();
        int reward = preferenceQueries.size();
        for (String query : preferenceQueries)
        {
            ArrayList<String> ids = getStringQuery(query);
            for (String id : ids)
            {
                prefRewards.put(id, reward);
            }
            reward--;
        }
        
        // Set negative reward for exclude list
        for (String query : excludeQueries)
        {
            ArrayList<String> ids = getStringQuery(query);
            for (String id : ids)
            {
                prefRewards.put(id, NEGATIVE_REWARD);
            }
        }
        
        ArrayList<Node> startNodes = new ArrayList<Node>();
        ArrayList<Node> endNodes = new ArrayList<Node>();
        
        for (Long id : sourceIds)
        {
            startNodes.add(graphDb.getNodeById(id));
        }
        
        for (Long id : destinationIds)
        {
            endNodes.add(graphDb.getNodeById(id));
        }
        
        if (REACHABILITY_INDEX)
        { 
            tx.success();
            
            removeStartNodes(startNodes, endNodes);
            removeEndNodes(startNodes, endNodes);

            tx = graphDb.beginTx();
        }
        
        // Create a new node start and connect it to every source node.
        Node s = graphDb.createNode();
        for (Node n : startNodes)
        {
            s.createRelationshipTo(n, RelTypes.Temp);
        }

        // Create a new node end and connect it to every destination node.
        Node t = graphDb.createNode();
        for (Node n : endNodes)
        {
            n.createRelationshipTo(t, RelTypes.Temp);
        }

        pathCosts = new HashMap<ArrayList<Relationship>, int[]>();
        lbMap = new HashMap<Node, Integer>();
        lbMap.put(t, 0);
        ubMap = new HashMap<Node, Integer>();
        ubMap.put(t, 0);
        succMap = new HashMap<Node, Relationship[]>();
        HashSet<ArrayList<Relationship>> skyline = new HashSet<ArrayList<Relationship>>();
        AbstractCollection<Node> open;
        
        if (PRIORITY_QUEUE)
        {
            open = new PriorityQueue<Node>(1000, new NodeComparator());
        }
        else
        {
            open = new HashSet<Node>();
        }
            
        open.add(t);
        
        long loopStartTime = System.currentTimeMillis();
        long currentTime = System.currentTimeMillis();
        while (!open.isEmpty() && (currentTime - loopStartTime) < TIME_OUT)
        {
            Node n = null;
            
            if (PRIORITY_QUEUE) 
            {
                n = ((PriorityQueue<Node>) open).poll();
            }
            else 
            {
                long min = Long.MAX_VALUE;
                for (Node e : open) 
                {
                    long sum = lb(e) - ub(e);
                    if (sum < min) 
                    {
                        min = sum;
                        n = e;
                    }
                }
              open.remove(n);  
            }            
            
            // Skip node expansion if subpath is globally dominated
            if (globallyDominated(n, skyline))
            {
                continue;
            }
            
            // Node expansion
            Iterator<Relationship> it = n.getRelationships(Direction.INCOMING).iterator();
            while (it.hasNext()) 
            {
                boolean sLbModified = false;
                boolean sUbModified = false;
                Relationship edge = it.next();
                Node m = edge.getStartNode();

                int[] costs = cost(edge, m);
                
                int upperBound = ub(n) +  costs[UPPER_BOUND];
                if (upperBound > ub(m)) 
                {                   
                    // Check path length to avoid very long paths
                    int count = 1;
                    Relationship[] rs = succMap.get(n);
                    while (rs != null && rs[UPPER_BOUND] != null) 
                    {
                        Relationship r = rs[UPPER_BOUND];
                        rs = succMap.get(r.getEndNode());   
                        count++;
                        if (count > (MAX_HOPS)) 
                        {
                            break;
                        }
                    }
                    
                    if (count <= (MAX_HOPS)) 
                    {
                        ubMap.put(m, upperBound);
                        Relationship[] msucc = succ(m);
                        msucc[UPPER_BOUND] = edge;
                        succMap.put(m, msucc);
                        if (m.equals(s)) 
                        {
                            sUbModified = true;
                        }
                        else 
                        {
                            if (PRIORITY_QUEUE) 
                            {
                                open.remove(m);
                            }
                            open.add(m);
                        }
                    }
                }

                int lowerBound = lb(n) + costs[LOWER_BOUND];
                if (lowerBound < lb(m)) 
                {
                    lbMap.put(m, lowerBound);
                    Relationship[] msucc = succ(m);
                    msucc[LOWER_BOUND] = edge;
                    succMap.put(m, msucc);
                    if (m.equals(s)) 
                    {
                        sLbModified = true;                          
                    }
                    else 
                    {
                        if (PRIORITY_QUEUE) 
                        {
                            open.remove(m);
                        }
                        open.add(m);
                    }
                }
                
                // Path construction
                if (sLbModified || sUbModified)
                {
                    if (sLbModified)
                    {
                        ArrayList<Relationship> p = reconstructPath(s, t, LOWER_BOUND);
                        if (!pathGloballyDominated(p, skyline)) 
                        {
                            ArrayList<ArrayList<Relationship>> toRemove = new ArrayList<ArrayList<Relationship>>();
                            for (ArrayList<Relationship> path : skyline) 
                            {
                                if (pathDominatedBy(path, p)) 
                                {
                                    toRemove.add(path);
                                }
                            }
                            for (ArrayList<Relationship> path : toRemove) 
                            {
                                skyline.remove(path);
                            }
                            skyline.add(p);
                        }
                    }
                    if (sUbModified)
                    {
                        ArrayList<Relationship> p = reconstructPath(s, t, UPPER_BOUND);
                        if (!pathGloballyDominated(p, skyline)) 
                        {
                            ArrayList<ArrayList<Relationship>> toRemove = new ArrayList<ArrayList<Relationship>>();
                            for (ArrayList<Relationship> path : skyline) 
                            {
                                if (pathDominatedBy(path, p)) 
                                {
                                    toRemove.add(path);
                                }
                            }
                            for (ArrayList<Relationship> path : toRemove) 
                            {
                                skyline.remove(path);
                            }
                            skyline.add(p);
                        }
                    }
                }
            }

            currentTime = System.currentTimeMillis();  
        }
            
        // Remove temp edges from paths
        for (ArrayList<Relationship> path : skyline) {
            path.remove(path.size() - 1);
            path.remove(0);
        }
        
        for (ArrayList<Relationship> path : skyline) {
            printPath(path);
        }
        
        deleteTempRels(s, t);
        
        tx.success();
        tx.close();
    }   
    
    public void setReachabilityIndex(ReachabilityIndex idx)
    {
        index = idx;
    }

    private ArrayList<Relationship> reconstructPath(Node s, Node t, int i)
    {
        Node m = s;
        ArrayList<Relationship> p = new ArrayList<Relationship>();
        HashMap<Relationship, Boolean> visited = new HashMap<Relationship, Boolean>();
        while (!m.equals(t))
        {
            Relationship edge = succ(m)[i];
            if (visited.get(edge) != null)
            {
                break;
            }
            p.add(edge);
            visited.put(edge, true);
            m = edge.getEndNode();
        }
        return p;
    }
    
    private int[] cost(Relationship rel, Node m) {
        int totalLength = 1;
        int totalCost = 0;
        Integer relCost = prefRewards.get(rel.getType().name());
        Integer nodeCost = prefRewards.get(m.getId() + "");
        
        if (relCost != null)
        {
            totalCost += relCost;
            if (relCost <= NEGATIVE_REWARD)
            {
                totalLength += -relCost;
            }
        }
        if (nodeCost != null)
        {
            totalCost += nodeCost;
            if (nodeCost <= NEGATIVE_REWARD)
            {
                totalLength += -nodeCost;
            }
        }

        int[] cost = {totalLength, totalCost};
        return cost;
    }
    
    private boolean globallyDominated(Node n, HashSet<ArrayList<Relationship>> S)
    {
        if (S.isEmpty()) {
            return false;
        }
        
        int nLb = lb(n);
        int nUb = ub(n);
        ArrayList<int[]> bounds = new ArrayList<int[]>();
        
        for (ArrayList<Relationship> path : S) {
            Node m = path.get(0).getEndNode();
            int[] bound = {lb(m), ub(m)};
            bounds.add(bound);
        }
        
        for (int[] bound : bounds) {
            if (nLb > bound[LOWER_BOUND]) {
                if (nUb <= bound[UPPER_BOUND]) {
                    return true;
                }
            } 
            else if (nUb < bound[UPPER_BOUND]) {
                if (nLb >= bound[LOWER_BOUND]) {
                    return true;
                }
            }
        }
        
        return false;
    }
    
    private boolean pathGloballyDominated(ArrayList<Relationship> p, HashSet<ArrayList<Relationship>> S)
    {
        if (S.isEmpty()) {
            return false;
        }
        
        ArrayList<int[]> bounds = new ArrayList<int[]>();
        for (ArrayList<Relationship> path : S) {
            int[] bound = getPathBounds(path);
            bounds.add(bound);
        }

        int[] nBound = getPathBounds(p);
        
        for (int i = 0; i < bounds.size(); i++) {
            int[] bound = bounds.get(i);

            if (nBound[LOWER_BOUND] >= bound[LOWER_BOUND]) 
            {
                if (nBound[UPPER_BOUND] <= bound[UPPER_BOUND]) 
                {
                    return true;
                }
            }
        }
        return false;
    }
    
    private int[] getPathBounds(ArrayList<Relationship> path)
    {
        int[] bounds = pathCosts.get(path);
        if (bounds == null)
        {
            int pathLength = 0;
            int pathCost = 0;
            for (Relationship r : path)
            {
                Node m = r.getEndNode();
                int[] costs = cost(r, m);
                pathLength += costs[0];
                pathCost += costs[1];
            }
            bounds = new int[2];
            bounds[LOWER_BOUND] = pathLength;
            bounds[UPPER_BOUND] = pathCost;
            pathCosts.put(path, bounds);
        }
        return bounds;
    }
    
    private boolean pathDominatedBy(ArrayList<Relationship> p1, ArrayList<Relationship> p2) 
    {
        int[] bounds1 = getPathBounds(p1);
        int[] bounds2 = getPathBounds(p2);
        
        if (bounds1[LOWER_BOUND] >= bounds2[LOWER_BOUND]) 
        {
            if (bounds1[UPPER_BOUND] <= bounds2[UPPER_BOUND]) 
            {
                return true;
            }
        }
        return false;
    }
    
    private int lb(Node n) 
    {
        Integer lb = lbMap.get(n);
        if (lb == null) 
        {
            lb = INITIAL_LOWER_BOUND;
            lbMap.put(n, lb);
        }
        return lb;
    }
    
    private int ub(Node n) 
    {
        Integer ub = ubMap.get(n);
        if (ub == null) 
        {
            ub = INITIAL_UPPER_BOUND;
            lbMap.put(n, ub);
        }
        return ub;
    }
    
    private Relationship[] succ(Node n) 
    {
        Relationship[] succ = succMap.get(n);
        if (succ == null) 
        {
            succ = new Relationship[2];
            succMap.put(n, succ);
        }
        return succ;
    }
    
    private ArrayList<Long> getIdsQuery(String query) 
    {
        Result result = graphDb.execute(query);
        ArrayList<Long> ids = new ArrayList<Long>();
        
        while (result.hasNext())
        {
            Map<String,Object> row = result.next();
            for (Entry<String,Object> column : row.entrySet())
            {
                ids.add((Long) column.getValue());
            }
        }
        return ids;
    }
    
    private ArrayList<String> getStringQuery(String query) 
    {
        Result result = graphDb.execute(query);
        ArrayList<String> ids = new ArrayList<String>();
        
        while (result.hasNext())
        {
            Map<String,Object> row = result.next();
            for (Entry<String,Object> column : row.entrySet())
            {
                ids.add((String) column.getValue());
            }
        }
        return ids;
    }
    
    private void printPath(ArrayList<Relationship> path) {
        try {
        if (path.size() == 0) {
            System.out.println("empty path");
            return;
        }
        int nodes = 1, pref1 = 0, pref2 =0;
        StringBuilder sb = new StringBuilder();
        sb.append("(" + path.get(0).getStartNode() + " " + path.get(0).getStartNode().getLabels().iterator().next() + ")");
        int cost = 0;
        for (int i = 0; i < path.size(); i++) 
        {
            Relationship r = path.get(i);
            Node n = r.getEndNode();
            
            sb.append("--[" + (path.get(i)).getType() + "]-->(" + n + " " + n.getLabels().iterator().next() + ")");
            Integer c = prefRewards.get(n.getId() + "");
            Integer relCost = prefRewards.get(r.getType().name());
            
            if (relCost != null) 
            {
                cost += relCost;
            }
            
            if (c != null) 
            {
                cost += c;
                if (cost == 2 * numPrefs)
                    pref1++;
                else //if (cost == -4)
                    pref2++;
            }
            nodes++;
        }
        
        System.out.println(sb);
        System.out.println("Reward: " + cost);
        System.out.println("Total nodes: " + nodes + " Pref1: " + pref1 + " Pref2: " + pref2);
        } catch(NullPointerException e) {e.printStackTrace();}
    }
    
    private void printPathNoRewards(ArrayList<Relationship> path) {
        try {
        if (path.size() == 0) {
            System.out.println("empty path");
            return;
        }
        int nodes = 1, pref1 = 0, pref2 =0;
        StringBuilder sb = new StringBuilder();
        sb.append("(" + path.get(0).getStartNode() + " " + path.get(0).getStartNode().getLabels().iterator().next() + ")");
        int cost = 0;
        for (int i = 0; i < path.size(); i++) 
        {
            Relationship r = path.get(i);
            Node n = r.getEndNode();
            
            sb.append("--[" + (path.get(i)).getType() + "]-->(" + n + " " + n.getLabels().iterator().next() + ")");
        }
        
        System.out.println(sb);
        } catch(NullPointerException e) {e.printStackTrace();}
    }
    
    private void deleteTempRels(Node start, Node end)
    {
        Iterable<Relationship> rels = start.getRelationships(Direction.OUTGOING);
        for (Relationship r : rels) 
        {
            r.delete();
        }
        start.delete();
        
        rels = end.getRelationships(Direction.INCOMING);
        for (Relationship r : rels) 
        {
            r.delete();
        }
        end.delete();
    }
    
    private void removeEndNodes(ArrayList<Node> startNodes, ArrayList<Node> endNodes)
    {
        for (int i = 0; i < endNodes.size(); i++)
        {
            Node endNode = endNodes.get(i);
            boolean canReach = false;
            for (Node startNode : startNodes)
            {
                if (index.canReach(startNode, endNode))
                {
                    canReach = true;
                    break;
                }
            }
            if (!canReach)
            {
                endNodes.remove(endNode);
                i--;
            }
        }
    }
    
    private void removeStartNodes(ArrayList<Node> startNodes, ArrayList<Node> endNodes)
    {        
        for (int i = 0; i < startNodes.size(); i++)
        {
            Node startNode = startNodes.get(i);
            boolean canReach = false;
            for (Node endNode : endNodes)
            {
                if (index.canReach(startNode, endNode))
                {
                    canReach = true;
                    break;
                }
            }
            if (!canReach)
            {
                startNodes.remove(startNode);
                i--;
            }
        }
    }
    
    void createDb() throws IOException
    {
        //FileUtils.deleteRecursively( new File( DB_PATH ) );

        graphDb = new GraphDatabaseFactory().newEmbeddedDatabaseBuilder( DB_PATH ).
                newGraphDatabase();
        registerShutdownHook( graphDb );
        System.out.println("Database loaded\n");
    }
    
    void shutDown()
    {
        System.out.println();
        System.out.println( "Shutting down database ..." );
        graphDb.shutdown();
    }
    
    private static void registerShutdownHook( final GraphDatabaseService graphDb )
    {
        // Registers a shutdown hook for the Neo4j instance so that it
        // shuts down nicely when the VM exits (even if you "Ctrl-C" the
        // running application).
        Runtime.getRuntime().addShutdownHook( new Thread()
        {
            @Override
            public void run()
            {
                graphDb.shutdown();
            }
        } );
    }
      
    class NodeComparator implements Comparator<Node>
    {
        @Override
        public int compare(Node n1, Node n2)
        {
            return lb(n1) - lb(n2);
        }
    }
    
    public void sequencePathQuery(String startNodesQuery, String endNodesQuery, ArrayList<String> midPointsQueries) 
    {
        tx = graphDb.beginTx();

        ArrayList<Long> sourceIds = getIdsQuery(startNodesQuery);
        ArrayList<Long> destinationIds = getIdsQuery(endNodesQuery);

        ArrayList<ArrayList<Long>> midPointsIds = new ArrayList<ArrayList<Long>>();
        for (String query : midPointsQueries)
        {
            ArrayList<Long> ids = getIdsQuery(query);
            midPointsIds.add(ids);
        }
        
        ArrayList<Node> startNodes = new ArrayList<Node>();
        ArrayList<Node> middleNodes = new ArrayList<Node>();
        ArrayList<Node> endNodes = new ArrayList<Node>();
        
        for (Long id : sourceIds) 
        {
            startNodes.add(graphDb.getNodeById(id));
        }
        
        for (Long id : midPointsIds.get(0)) 
        {
            middleNodes.add(graphDb.getNodeById(id));
        }
        
        for (Long id : destinationIds) 
        {
            endNodes.add(graphDb.getNodeById(id));
        }
        
        tx.success();

        removeStartNodes(startNodes, middleNodes);
        removeEndNodes(startNodes, middleNodes);
        
        ArrayList<Node> prevNodes = null;
        
        if (midPointsIds.size() > 1) 
        {
            prevNodes = (ArrayList<Node>) middleNodes.clone();
            
            for (int i = 1; i < midPointsIds.size(); i++) 
            {
                middleNodes = new ArrayList<Node>();
                for (Long id : midPointsIds.get(i)) 
                {
                    middleNodes.add(graphDb.getNodeById(id));
                }
                removeStartNodes(prevNodes, middleNodes);
                removeEndNodes(prevNodes, middleNodes);
            }
        }
        
        removeStartNodes(middleNodes, endNodes);        
        removeEndNodes(middleNodes, endNodes);

        tx = graphDb.beginTx();
        
        Node start = graphDb.createNode();
        for (Node n : startNodes) 
        {
            start.createRelationshipTo(n, RelTypes.Temp);
        }
        
        middleNodes = new ArrayList<Node>();
        for (Long id : midPointsIds.get(0)) 
        {
            middleNodes.add(graphDb.getNodeById(id));
        }

        Node end = graphDb.createNode();
        for (Node n : middleNodes) 
        {
            n.createRelationshipTo(end, RelTypes.Temp);
        }
        
        PathFinder<Path> finder = GraphAlgoFactory.shortestPath(PathExpanders.forDirection(Direction.OUTGOING), 15);

        ArrayList<ArrayList<ArrayList<Relationship>>> paths = new ArrayList<ArrayList<ArrayList<Relationship>>>();
        paths.add(findPaths(start, end, finder));
            
        ArrayList<Node> m1 = new ArrayList<Node>();
        
        for (ArrayList<Relationship> path : paths.get(0)) 
        {
            m1.add(path.get(path.size()-1).getEndNode());
        }
          
        deleteTempRels(start, end);
        
        
        if (midPointsIds.size() > 1)
        {
            for (int i = 1; i < midPointsIds.size(); i++)
            {
                start = graphDb.createNode();
                for (Node n : m1) {
                    start.createRelationshipTo(n, RelTypes.Temp);
                }

                ArrayList<Node> m2 = new ArrayList<Node>();
                
                for (Long id : midPointsIds.get(i)) 
                {
                    m2.add(graphDb.getNodeById(id));
                }
                
                end = graphDb.createNode();
                for (Node n : m2) {
                    n.createRelationshipTo(end, RelTypes.Temp);
                }

                ArrayList<ArrayList<Relationship>> path = findPaths(start, end, finder);
                paths.add(path);
                
                m1 = new ArrayList<Node>();
                
                for (ArrayList<Relationship> p : path) {
                    m1.add(p.get(p.size()-1).getEndNode());
                }
              
                deleteTempRels(start, end);
            }
        }
        
        start = graphDb.createNode();
        for (Node n : m1) {
            start.createRelationshipTo(n, RelTypes.Temp);
        }
     
        
        end = graphDb.createNode();
        
        for (Node n : endNodes) {
            n.createRelationshipTo(end, RelTypes.Temp);
        }
        
        paths.add(findPaths(start, end, finder));
        
        // The following code only works when there is two middle regions.
        // TO DO: Make it work generically.
        
        // Find matching path
        boolean pathFound = false;
        for (ArrayList<Relationship> path3 : paths.get(2)) 
        {
            Node n3Start = path3.get(0).getStartNode();
            for (ArrayList<Relationship> path2 : paths.get(1)) 
            {
                Node n2End = path2.get(path2.size()-1).getEndNode();
                if (n3Start.equals(n2End)) 
                {
                    Node n2Start = path2.get(0).getStartNode();
                    for (ArrayList<Relationship> path1 : paths.get(0)) 
                    {
                        Node n1End = path1.get(path1.size()-1).getEndNode();
                        if (n2Start.equals(n1End)) 
                        {
                            printPathNoRewards(path1);
                            printPathNoRewards(path2);
                            printPathNoRewards(path3);
                            pathFound = true;
                            break;
                        }
                    }
                    if (pathFound)
                        break;
                }
            }
            if (pathFound)
                break;
        }
        
        deleteTempRels(start, end);
        
        tx.success();
        tx.close();
    }
    
    private ArrayList<ArrayList<Relationship>> findPaths(Node start, Node end, PathFinder<Path> finder)
    {
        ArrayList<ArrayList<Relationship>> paths = new ArrayList<ArrayList<Relationship>>();
        Iterator<Path> p = finder.findAllPaths(start, end).iterator();
        while (p.hasNext())
        {
            Iterator<Relationship> relationshipsIt = p.next().relationships().iterator();
            ArrayList<Relationship> path = new ArrayList<Relationship>();
            
            while (relationshipsIt.hasNext()) 
            {
                path.add(relationshipsIt.next());
            }
            path.remove(0);
            path.remove(path.size()-1);
            paths.add(path);
        }
        return paths;
    }
}
