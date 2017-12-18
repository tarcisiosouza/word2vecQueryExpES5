package de.l3s.souza.evaluation;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.StringTokenizer;

/**
 * Class to read documents
 *
 * @authors Mubin Shrestha, Tarcisio Souza
 * 
 */
public class DocumentParser {

    //This variable will hold all terms of each document in an array.
    private List<String[]> termsDocsArray = new ArrayList<String[]>();
    private HashSet<String> stopwords = new HashSet<String>(); 
    private double[] tfidfVector;
    private List<String[]> termsDocArray = new ArrayList<String[]>();
    private List<String> allTerms = new ArrayList<String>(); //to hold all terms
    private List<double[]> tfidfDocsVector = new ArrayList<double[]>();
    private HashMap<String,Integer> fileNames = new  HashMap<String,Integer>();
  
    /**
     * Method to read files and store in array.
     * @param filePath : source file path
     * @throws FileNotFoundException
     * @throws IOException
     */
    
    public DocumentParser ()
    {
    	
      	 try 
   	   	  {
   	   	   File fl = new File("/home/souza/workspace/deepLearningSeedFinder/stopwords.txt");
      	//	File fl = new File("/home/souza/stopwords_de.txt");
   	   	   BufferedReader br = new BufferedReader(new FileReader(fl)) ;
   	   	   String string;
   	   	   while ((string=br.readLine())!=null)
   	   	   {
   	   		   stopwords.add(string);
   	   	   }
   	   	   br.close();
   	   	   
   	   	  }
   	   	  catch (IOException  e)
   	   	  { e.printStackTrace(); }
    	
    }
    
    //calculate similarity given a pair of documents
    public double SimilarityPairDocuments (String text1, String text2)
    {
    	double similarity = 0.0f;
    	
    	String[]docTermsText1;
    	String[]docTermsText2;
    	
    	allTerms.clear();
    	termsDocsArray.clear();
    	
    	docTermsText1 = addTermsFromDocument (removeStopWords (text1));
    	docTermsText2 = addTermsFromDocument (removeStopWords (text2));
    	
    	double[] tfidfText1 = tfIdfVectorGenerator (docTermsText1);
    	double[] tfidfText2 = tfIdfVectorGenerator (docTermsText2);
    	
    	similarity = new CosineSimilarity().cosineSimilarity(tfidfText1, tfidfText2);
    	return similarity;
    	
    }
    
    //get the highest similarity comparing with a collection of documents
    public double getHigherScoreSimilarity (String text1, HashSet<String> collection) throws Exception
    {
   	 double currentHigher = 0.0f;
   	 
   	for (String s : collection) {
   		double current = SimilarityPairDocuments (text1,s);
   		if (current > currentHigher)
   			currentHigher = current;
   	}
   	 
   	 return currentHigher;
   	 
    }
    
    public String[] addTermsFromDocument (String text)
    {
    	String[] tokenizedTerms = text.replaceAll("[\\W&&[^\\s]]", "").split("\\W+"); 
   	 	for (String term : tokenizedTerms) {
            if (!allTerms.contains(term)) {  //avoid duplicate entry
                allTerms.add(term);
            }
        }
   	 	
   	 	termsDocsArray.add(tokenizedTerms);
   	 	return tokenizedTerms;
   	 	
    	
    }
    public String removeStopWords (String str)
	{
		String newStr="";
		//String input = str.replaceAll("[-+.^:,]","");
		
		StringTokenizer token = new StringTokenizer (str);
		while (token.hasMoreTokens())
		{
			String term = token.nextToken().toLowerCase();
			if (!stopwords.contains(term) && term.length()>1)
			{
				newStr = newStr + " " +term;
			}
		}
		return newStr;
	}
    
    //parse a collection in separated files
    public void parseFiles(String filePath,HashMap<Integer,Integer> relevance) throws FileNotFoundException, IOException {
        File[] allfiles = new File(filePath).listFiles();
        BufferedReader in = null;
        int i = 0;
        int size = allfiles.length;
        String filteredDocument;
        
        for (File f : allfiles) {
            if (f.getName().endsWith(".txt")) {
                in = new BufferedReader(new FileReader(f));
                StringBuilder sb = new StringBuilder();
                String s = null;
                while ((s = in.readLine()) != null) {
                    sb.append(s);
                }
                
                filteredDocument = removeStopWords(sb.toString());
                String[] tokenizedTerms = filteredDocument.replaceAll("[\\W&&[^\\s]]", "").split("\\W+");   //to get individual terms
                for (String term : tokenizedTerms) {
                    if (!allTerms.contains(term)) {  //avoid duplicate entry
                        allTerms.add(term);
                    }
                }
                int docId = 0;
            try {  
                StringTokenizer token = new StringTokenizer (f.getName(),"_");
                docId = Integer.parseInt(token.nextToken());
                int docRel = Integer.parseInt(token.nextToken());
            } catch (Exception e)
            {
            	docId = i;
            }
                termsDocsArray.add(tokenizedTerms);
              //  fileNames.put(f.getName(),relevance.get(docId));
                i++;
               
            }
        }

    }

	/**
     * Method to create termVector according to its tfidf score.
     */
    public void tfIdfCalculator() {
        double tf; //term frequency
        double idf; //inverse document frequency
        double tfidf; //term requency inverse document frequency        
        for (String[] docTermsArray : termsDocsArray) {
            double[] tfidfvectors = new double[allTerms.size()];
            int count = 0;
            for (String terms : allTerms) {
                tf = new TfIdf().tfCalculator(docTermsArray, terms);
                idf = new TfIdf().idfCalculator(termsDocsArray, terms);
                tfidf = tf * idf;
                tfidfvectors[count] = tfidf;
                count++;
            }
            tfidfDocsVector.add(tfidfvectors);  //storing document vectors;            
        }
    }
    
    public double[] tfIdfVectorGenerator (String[] docTermsArray)
    {
    	  double tf; //term frequency
          double idf; //inverse document frequency
          double tfidf; //term requency inverse document frequency  
          double[] tfidfvectors = new double[allTerms.size()];
          int count = 0;
          
          for (String terms : allTerms) {
            tf = new TfIdf().tfCalculator(docTermsArray, terms);
            idf = new TfIdf().idfCalculator(termsDocsArray, terms);
            tfidf = tf * idf;
            tfidfvectors[count] = tfidf;
            count++;
          }
          return tfidfvectors;
    }
    

    /**
     * Method to calculate cosine similarity between all the documents.
     */
    public void getCosineSimilarity() {
        for (int i = 0; i < tfidfDocsVector.size(); i++) {
            for (int j = 0; j < tfidfDocsVector.size(); j++) {
                System.out.println("between " + i + " and " + j + "  =  "
                                   + new CosineSimilarity().cosineSimilarity
                                       (
                                         tfidfDocsVector.get(i), 
                                         tfidfDocsVector.get(j)
                                       )
                                  );
            }
        }
    }


	public List<String[]> getTermsDocsArray() {
		return termsDocsArray;
	}

	public void setTermsDocsArray(List<String[]> termsDocsArray) {
		this.termsDocsArray = termsDocsArray;
	}

	public List<double[]> getTfidfDocsVector() {
		return tfidfDocsVector;
	}

	public void setTfidfDocsVector(List<double[]> tfidfDocsVector) {
		this.tfidfDocsVector = tfidfDocsVector;
	}

	public HashMap<String,Integer> getFileNames() {
		return fileNames;
	}

	
}


