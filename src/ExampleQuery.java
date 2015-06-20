import java.io.IOException;
import java.util.ArrayList;


public class ExampleQuery {
    
    public static void main(String[] args) throws IOException, InterruptedException 
    {
        PreferencePaths db = new PreferencePaths();
        db.createDb();
        
        ReachabilityIndex index = new ReachabilityIndex(graphDb);
        if (!index.indexExists()) 
        {
            index.createIndex(); 
        }
        
        String startNodesQuery = "match (a:Person)-[:IsLocatedIn]->(b:Place)-[:IsPartOf]->(c:Place) where c.name=\"Japan\" return id(a)";
        String endNodesQuery = "match (a:Person)-[:IsLocatedIn]->(b:Place)-[:IsPartOf]->(c:Place) where c.name=\"United_States\" return id(a)";
        
        ArrayList<String> preferenceQueries = new ArrayList<String>();
        preferenceQueries.add("match (n:Post) return str(id(n))");
        preferenceQueries.add("match ()-[r:Knows]->() return type(r) limit 1");

        ArrayList<String> excludeQueries = new ArrayList<String>();
        excludeQueries.add("match ()-[r:ReplyOf]->() retun type(r) limit 1");
          
        long startTime = System.currentTimeMillis();
        
        db.setReachabilityIndex(index);
        db.preferencePathQuery(startNodesQuery, endNodesQuery, preferenceQueries, excludeQueries, index);

        long endTime = System.currentTimeMillis();
        long elapsed = endTime - startTime;
        long minutes = elapsed / (1000 * 60);
        long seconds = (elapsed / 1000) - (minutes * 60);
        long tenths = (elapsed / 100) - (seconds * 10);
        System.out.println("\nTotal execution took " + minutes + " m " + seconds + "." + tenths + " s \n");

        db.shutDown();
    }    

}
