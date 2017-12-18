package de.l3s.souza.word2vecseedfinder;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.net.MalformedURLException;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.StringTokenizer;

import de.l3s.souza.esfive.Article;
import de.l3s.souza.deeplearning.Word2VecUptraining;

public class deepLearningUtils {

	private Word2VecUptraining word2Vec;
	private BufferedWriter bw;
	private HashSet<String> stopwords;
	private String fileNameArticles;
	
	public deepLearningUtils(String fileName) throws IOException {
		
		fileNameArticles = fileName;
		bw = new BufferedWriter(new FileWriter(fileNameArticles, true));
		word2Vec = new Word2VecUptraining ();
		stopwords = new HashSet<String>();
		
		 try 
	   	  {
	   	   File fl = new File("/home/souza/stopwords_de.txt");
	   	   BufferedReader br = new BufferedReader(new FileReader(fl)) ;
	   	   String str;
	   	   while ((str=br.readLine())!=null)
	   	   {
	   		   stopwords.add(str);
	   	   }
	   	   br.close();
	   	   
	   	  }
	   	  catch (IOException  e)
	   	  { e.printStackTrace(); }
	}

	public void closeFiles () throws IOException
	{
		bw.close();
	}
	
	public void loadModel (String fileName)
	{
		 word2Vec.loadModel(fileName);
	}
	
	public void train (String path)
	{
		word2Vec.train(path);
	}
	
	public void trainRetrievedDocuments(HashMap<String,Article> art, String path) throws MalformedURLException {
		
	/*	 for(Entry<String, Article> s : art.entrySet())
		 {
			 String finalStr = removeStopWords(s.getValue().getText());
			 appendToFile ( finalStr );
		
		 }*/
		 word2Vec.train(path);		 

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
	
	public Collection<String> getWordsNearest (String keyword,int total)
	{
		return word2Vec.getWordsNearest(keyword, total);
	}
	
	public double getCosSimilarity (String word1,String word2)
	{
		return word2Vec.getCosSimilarity(word1, word2);
	}
	
	public void appendToFile (String strToapped) 
	{
		 
	      try {
	        
	     bw.write(strToapped);
	     bw.newLine();
	     bw.flush();
	      
	      } catch (IOException ioe) {
	    	  ioe.printStackTrace();
	      } 
	    
	}
	
	public void resetFile () throws IOException
	{
		bw = new BufferedWriter(new FileWriter(fileNameArticles, true));
	}

	public HashSet<String> getStopwords() {
		return stopwords;
	}

	public void setStopwords(HashSet<String> stopwords) {
		this.stopwords = stopwords;
	}
	
	public boolean isStopWord (String keyword)
	{
		
		if (stopwords.contains(keyword))
			return true;
		return false;
	}
}
