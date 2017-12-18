package de.l3s.souza.learningtorank;

import java.io.File;

import ciir.umass.edu.eval.Evaluator;
import ciir.umass.edu.learning.RANKER_TYPE;
import ciir.umass.edu.learning.RankList;
import ciir.umass.edu.learning.Ranker;
import ciir.umass.edu.learning.RankerFactory;
import ciir.umass.edu.metric.METRIC;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for simple App.
 */
public class AppTest 
    extends TestCase
{
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public AppTest( String testName )
    {
        super( testName );
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite()
    {
        return new TestSuite( AppTest.class );
    }

    /**
     * Rigourous Test :-)
     * @throws Exception 
     */
    public void testApp() throws Exception
    {
    	Evaluator ev = new Evaluator (RANKER_TYPE.LAMBDAMART,METRIC.MAP,METRIC.MAP);
    	
       	//ev.score("/home/souza/RankLib/models_shuffled/f5.cas", "/home/souza/RankLib/score_testing.txt", "output.txt");
    	String output = ev.rankToString("/home/souza/mymodels/f3.cas", "0 qid:025f 1:19.0 2:2.944439 3:7.0 4:1.9459101 5:3.218876 6:1.1690322 7:0.0 8:0.0 9:0.0 10:0.0 11:0.0 12:0.0 13:0.0 14:0.0 15:0.0 16:0.0 17:61.15864 18:4.113471 19:4.890349 #sister");
    	System.out.println(output);
    	
    }
}
