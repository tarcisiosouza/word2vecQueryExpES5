package de.l3s.souza.evaluation;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import org.apache.commons.math3.stat.correlation.PearsonsCorrelation;

/**
 *
 * @author Mubin Shrestha
 */
public class TfIdfMain {
    
    /**
     * Main method
     * @param args
     * @throws FileNotFoundException
     * @throws IOException 
     */
	 private static List<double[]> tfidfDocsElastic;
	 private static List<double[]> tfidfDocsUser;
	 private static HashMap<Integer,Integer> relevance;
	 private static HashMap<String,Integer> ElasticFileNames = new HashMap<String,Integer>();
	 private static HashMap<String,Integer>  UserFileNames = new HashMap<String,Integer> ();
	 
    public static void main(String args[]) throws Exception
    {
    	
        DocumentParser dpElastic = new DocumentParser();
       
        
        dpElastic.parseFiles("/home/souza/articles/test",relevance);
        
    /*    File f = new File ("/home/souza/Article_10.txt");
        FileReader fr = new FileReader (f);
        BufferedReader br = new BufferedReader (fr);
        String line;
        String document = "";
        while ((line = br.readLine())!=null)
        {
        	document = document + line;
        }
        
        dpElastic.parseDocument(document);
        */
        dpElastic.tfIdfCalculator();
        //dpElastic.tfIdfCalculatorDocument();
        //ElasticFileNames =  dpElastic.getFileNames();
        
       // tfidfDocsElastic= dpElastic.getTfidfDocsVector();
       
        dpElastic.getCosineSimilarity();
        //dpElastic.tfIdfCalculatorDocument(); //calculates tfidf
        //dpElastic.getCosineSimilarityDoc();
        
        int i = 0;
        int size = UserFileNames.size();

     }
    }
