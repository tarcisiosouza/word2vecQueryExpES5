package de.l3s.souza.word2vecseedfinder;

import de.l3s.souza.learningtorank.Term;
import de.l3s.souza.learningtorank.TermUtils;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for simple App.
 */
public class L2RfeaturesTest 
    extends TestCase
{
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public L2RfeaturesTest( String testName )
    {
        super( testName );
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite()
    {
        return new TestSuite( L2RfeaturesTest.class );
    }

    /**
     * Rigourous Test :-)
     * @throws Exception 
     */
    public void testApp() throws Exception
    {
    	Term term = new Term ("of");
    	TermUtils termUtils = new TermUtils ("001a","/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/",term,5,0.7,"1,2,3,4,5,6,7,8,9","nctir_11");
    //	term = termUtils.calculateL2Rfeatures("killers stress most");
    	System.out.println("");
    }
}