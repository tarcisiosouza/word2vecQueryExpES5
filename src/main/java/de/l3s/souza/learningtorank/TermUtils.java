package de.l3s.souza.learningtorank;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.StringTokenizer;

import de.l3s.souza.esfive.ElasticMain;
import de.l3s.souza.esfive.LivingKnowledgeSnapshot;
import de.l3s.souza.preprocess.PreProcess;
import de.l3s.souza.word2vecseedfinder.Query;

public class TermUtils {

	private String path;
	private Query queryObject;
	private static String topic;
	private static String features;
	private int pairCount = 0;
	private Term term;
	
	private String query;
	private HashSet<String> queryTerms = new HashSet<String>();
	private int windowSize;
	private int nDocuments=0;
	private int tf=0;
	private int pairCoOccurr =0;
	private int generalWindowSize = 5;
	private int coOcurr =0;
	private int df =0;
	private double lambda;
	private int termProx = 0;
	private boolean withinWindowSize = false;
	private int ftf = 0;
	private Query queryUtil;
	private ArrayList<Integer> positionsTerm = new ArrayList<Integer>();
	private ArrayList<Integer> positionsQueryTerms = new ArrayList<Integer>();
	private HashMap<LivingKnowledgeSnapshot,Double> feedbackDocuments = new HashMap<LivingKnowledgeSnapshot,Double> ();
	public TermUtils (String topic, String path, Term term, int windowSize,double lambda, String features,String ntcir) throws Exception
	{
		queryUtil = new Query (1,"id",ntcir);
		this.term = term;
		this.features = features;
		this.topic = topic;
		this.path = path;
		this.lambda = lambda;
		this.windowSize = windowSize;
		
	}
	
	public Term calculateL2Rfeatures (String queryString, Query queryObject,int totalFeedbackDocuments) throws Exception
	{
		
		this.query = queryString;
		this.queryObject = queryObject;
		StringTokenizer tokenQuery = new StringTokenizer (query);
		
		while (tokenQuery.hasMoreTokens())
		{
			String currentQueryTerm = tokenQuery.nextToken();
			//currentQueryTerm = preprocess.removeNonLettersString(currentQueryTerm);
			queryTerms.add(currentQueryTerm.toLowerCase());
		}

		calculateFeaturesCollection();
		
		windowSize = 15;
		nDocuments=0;
		tf=0;
		pairCoOccurr =0;
		coOcurr =0;
		df=0;
		termProx = 0;
		withinWindowSize = false;
		ftf = 0;
		
		calculateFeatures (query,totalFeedbackDocuments,"text",windowSize);
		term.setCoOcurrencyQueryPrf(coOcurr,15);
		term.setPairCoOccurQueryPrf(pairCoOccurr,16);
		term.setFeedbackTermFreq(tf,12);
		term.setLogFeedbackTermFreq(13);
	//	term.normalizeFeatures(features);
		return term;
	}

	public Term calculateL2Rfeatures (String queryString,int totalFeedbackDocuments) throws Exception
	{
		
		this.query = queryString;
		
		StringTokenizer tokenQuery = new StringTokenizer (query);
		
		while (tokenQuery.hasMoreTokens())
		{
			String currentQueryTerm = tokenQuery.nextToken();
			//currentQueryTerm = preprocess.removeNonLettersString(currentQueryTerm);
			queryTerms.add(currentQueryTerm.toLowerCase());
		}

		calculateFeaturesCollection();
		
		windowSize = 15;
		nDocuments=0;
		tf=0;
		pairCoOccurr =0;
		coOcurr =0;
		df=0;
		termProx = 0;
		withinWindowSize = false;
		ftf = 0;
		
		calculateFeatures (query,totalFeedbackDocuments,"text",windowSize);
		term.setCoOcurrencyQueryPrf(coOcurr,15);
		term.setPairCoOccurQueryPrf(pairCoOccurr,16);
		term.setFeedbackTermFreq(tf,12);
		term.setLogFeedbackTermFreq(13);
	//	term.normalizeFeatures(features);
		return term;
	}
	public static String getTopic() {
		return topic;
	}

	public void setTopic(String topic) {
		TermUtils.topic = topic;
	}

	public Term getTerm() {
		return term;
	}

	public void setTerm(Term term) {
		this.term = term;
	}

	public String getQuery() {
		return query;
	}

	public void setQuery(String query) {
		this.query = query;
		
		queryTerms.clear();
		StringTokenizer tokenQuery = new StringTokenizer (query);
		
		while (tokenQuery.hasMoreTokens())
		{
			String currentQueryTerm = tokenQuery.nextToken();
			//currentQueryTerm = preprocess.removeNonLettersString(currentQueryTerm);
			queryTerms.add(currentQueryTerm.toLowerCase());
		}
		
		final List<String> wordsQuery = Arrays.asList(query.split(" "));
		
	
	}

	private void calculateFeaturesCollection() throws Exception
	{

		String filePath = path + topic + "/" + topic + ".rel";
		df = 0;
		nDocuments = 0;
		
		double idf = 0.0f;
		boolean withinWindowSize;
		File f = new File (filePath);
		FileReader fr = new FileReader (f);
		BufferedReader br = new BufferedReader (fr);
		//term.setTermString(term.getTermString().toLowerCase());
		
		String line;
		
		while ((line = br.readLine()) != null)
		{
			withinWindowSize = false;
			StringTokenizer token = new StringTokenizer (line);
			while (token.hasMoreTokens())
			{
				String rel;
				String id;
						
				id = token.nextToken();
				rel = token.nextToken();
						
				calculateFeatures (id, 1, "id",1);
			}
		}
				
		term.setTf(tf,1);
		term.setLogTf(2);
		term.setDf(df,3);
		term.setLogDf(4);
		if (df==0)
			term.setIdf(0,5);
		else
			term.setIdf((double)Math.log(nDocuments/df),5);
			
		term.setLogIdf(6);
		term.setCoOcurrencyQuery(coOcurr,7);
		
		if (coOcurr==0)
			term.setLogCoOcurrencyQuery(0,8);
		else
			term.setLogCoOcurrencyQuery(Math.log(coOcurr)/queryTerms.size(),8);
		
		term.setPairCoOccurQuery(pairCoOccurr,9);
		
		if (pairCoOccurr==0)
			term.setLogPairCoCoccurQuery(0,10);
		else
			term.setLogPairCoCoccurQuery((double)Math.log(pairCoOccurr)/pairCount,10);
		term.setTermProximity(termProx,11);
		term.setTD(0.7,14);
		term.setTfIdf(17);
		term.setLogTfIdf(18);
		term.setLogTfDf(19);
		
		br.close();
	}
	
	private int calculatePairCoOcurr (ArrayList<Integer>queryTerms, ArrayList<Integer>terms)
	{
		int pairCoOccurr = 0;
		int j = 0;
		
		
		if (queryTerms.isEmpty() || terms.isEmpty())
			return 0;
		
		for (int i=0;i<queryTerms.size();i++)
		{
			if (i+1<queryTerms.size())
			{
				if ((Math.abs(queryTerms.get(i)-queryTerms.get(i+1)))<=1)
				{
					pairCount++;
					while (terms.get(j)<=queryTerms.get(i+1) && j<terms.size())
					{
						
						if ((Math.abs(terms.get(j)-queryTerms.get(i)))<=1 || (Math.abs(terms.get(j)-queryTerms.get(i+1)))<=1)
							pairCoOccurr++;
						j++;
						
						if (!(j<terms.size()))
								break;
					}
					
					if (!(j<terms.size()))
						break;
					
					if (Math.abs(terms.get(j)-queryTerms.get(i+1))<=1)
						pairCoOccurr++;
				}
			}
		}
		
		return pairCoOccurr;
	}
	
	private void calculateFeatures (String q, int limit, String field,int windowSize) throws Exception
	{
		
		if (limit==1)
		{
			queryObject.setCurrentQueryID(q);
			queryObject.setLimit(limit);
			queryObject.setField(field);
			queryObject.processCurrentQuery();
		}
		Map<LivingKnowledgeSnapshot, Double> documents = new HashMap<LivingKnowledgeSnapshot, Double>();
		
		documents = queryObject.getArticles();
		
		
		int i=0;
		int j=0;
		int distance=0;
		
		withinWindowSize = false;
		
		
		for (Entry<LivingKnowledgeSnapshot,Double> s : documents.entrySet())
		{
			
			positionsTerm.clear();
			positionsQueryTerms.clear();
			nDocuments++;
			String article = s.getKey().getText();
			
			String currentTerm = null;
			int position = 0;
			
			article = queryObject.getPreprocess().removeNonLettersFromText(article);
			
			if (article.contains(term.getTermString()))
			{
				df++;
				
				StringTokenizer tokenArticle = new StringTokenizer (article);
				
				while (tokenArticle.hasMoreTokens())
				{
					
					currentTerm = tokenArticle.nextToken();
					currentTerm = currentTerm.toLowerCase();
					
					if (currentTerm.contentEquals(term.getTermString().toLowerCase()))
					{
						tf++;
						positionsTerm.add(position);
						
					}
					
					if (queryTerms.contains(currentTerm.toLowerCase()))
					{
						positionsQueryTerms.add(position);
					}
					
					position++;
				}
				
				pairCoOccurr = calculatePairCoOcurr (positionsQueryTerms,positionsTerm);
				while (i<positionsQueryTerms.size() && j<positionsTerm.size())
				{
					if (positionsQueryTerms.get(i) <= positionsTerm.get(j))
					{
						
						distance = Math.abs(positionsQueryTerms.get(i) - positionsTerm.get(j));
						if (distance <= windowSize)
							coOcurr++;
						i++;
						
					}
					else
					{
						distance = Math.abs(positionsQueryTerms.get(i) - positionsTerm.get(j));
						if (distance <= windowSize)
							coOcurr++;
						
						j++;
					}
						
					if (distance <= generalWindowSize)	
						withinWindowSize = true;
				}
				
				break;
			}
		}
		
		if (withinWindowSize)		
			termProx++;
		
	}
	
	public HashMap<String,String> getCollection () throws IOException, Exception
	{
		
		Map<LivingKnowledgeSnapshot, Double> document = new HashMap<LivingKnowledgeSnapshot, Double>();
		
		HashMap<String,String> collection = new HashMap<String,String>();
		
		String filePath = path + topic + "/" + topic + ".rel";
		
		File f = new File (filePath);
		FileReader fr = new FileReader (f);
		BufferedReader br = new BufferedReader (fr);
		//term.setTermString(term.getTermString().toLowerCase());
		
		String line;
		
		while ((line = br.readLine()) != null)
		{
			
			StringTokenizer token = new StringTokenizer (line);
			while (token.hasMoreTokens())
			{
				String id;		
				id = token.nextToken();
				String rel = token.nextToken();
				queryUtil.setCurrentQueryID(id);
				queryUtil.setLimit(1);
				queryUtil.setTopic(topic);
				queryUtil.setField("id");
				queryUtil.processCurrentQuery();
				document = queryUtil.getArticles();
	
				for (Entry<LivingKnowledgeSnapshot,Double> s : document.entrySet())
				{
					collection.put(s.getKey().getDocId(), s.getKey().getText());
				}
			}
		}
		
		
		return collection;
		
	}
	public void calculateFeaturesCollectionOnline (HashMap<String,String> collec) throws Exception
	{
		
			df = 0;
			nDocuments = 0;
			
			int i=0;
			int j=0;
			int distance=0;
		
			withinWindowSize = false;
		
			for (Entry<String,String> s : collec.entrySet())
			{
			
							positionsTerm.clear();
							positionsQueryTerms.clear();
							nDocuments++;
							String article = s.getValue();
			
							String currentTerm = null;
							int position = 0;
			
							article = queryUtil.getPreprocess().removeNonLettersFromText(article);
			
							if (article.contains(term.getTermString()))
							{
								df++;
				
								StringTokenizer tokenArticle = new StringTokenizer (article);
				
								while (tokenArticle.hasMoreTokens())
								{
					
									currentTerm = tokenArticle.nextToken();
									currentTerm = currentTerm.toLowerCase();
					
									if (currentTerm.contentEquals(term.getTermString().toLowerCase()))
									{
										tf++;
										positionsTerm.add(position);
						
									}
					
									if (queryTerms.contains(currentTerm.toLowerCase()))
									{
										positionsQueryTerms.add(position);
									}
					
									position++;
								}
				
								pairCoOccurr = calculatePairCoOcurr (positionsQueryTerms,positionsTerm);
								while (i<positionsQueryTerms.size() && j<positionsTerm.size())
								{
									if (positionsQueryTerms.get(i) <= positionsTerm.get(j))
									{
						
										distance = Math.abs(positionsQueryTerms.get(i) - positionsTerm.get(j));
										if (distance <= windowSize)
											coOcurr++;
										i++;
						
									}
									else
									{
										distance = Math.abs(positionsQueryTerms.get(i) - positionsTerm.get(j));
										if (distance <= windowSize)
											coOcurr++;
						
										j++;
									}
						
									if (distance <= generalWindowSize)	
										withinWindowSize = true;
								}
				
								
							}
							
							if (withinWindowSize)		
								termProx++;
			}
		
					
			
			term.setTf(tf,1);
			term.setLogTf(2);
			term.setDf(df,3);
			term.setLogDf(4);
			if (df==0)
				term.setIdf(0,5);
			else
				term.setIdf((double)Math.log(nDocuments/df),5);
				
			term.setLogIdf(6);
			term.setCoOcurrencyQuery(coOcurr,7);
			
			if (coOcurr==0)
				term.setLogCoOcurrencyQuery(0,8);
			else
				term.setLogCoOcurrencyQuery(Math.log(coOcurr)/queryTerms.size(),8);
			
			term.setPairCoOccurQuery(pairCoOccurr,9);
			
			if (pairCoOccurr==0)
				term.setLogPairCoCoccurQuery(0,10);
			else
				term.setLogPairCoCoccurQuery((double)Math.log(pairCoOccurr)/pairCount,10);
			term.setTermProximity(termProx,11);
			term.setTD(0.7,14);
			term.setTfIdf(17);
			term.setLogTfIdf(18);
			term.setLogTfDf(19);
	}
	
	public void calculateFeaturesOnline (Map<LivingKnowledgeSnapshot, Double> documents, PreProcess preprocess) throws Exception
	{
		
		int i=0;
		int j=0;
		int distance=0;
		windowSize = 15;
		nDocuments=0;
		tf=0;
		pairCoOccurr =0;
		coOcurr =0;
		df=0;
		termProx = 0;
		withinWindowSize = false;
		ftf = 0;
		
		for (Entry<LivingKnowledgeSnapshot,Double> s : documents.entrySet())
		{
			
			positionsTerm.clear();
			positionsQueryTerms.clear();
			nDocuments++;
			String article = s.getKey().getText();
			
			String currentTerm = null;
			int position = 0;
			
			article = preprocess.removeNonLettersFromText(article);
			
			if (article.contains(term.getTermString()))
			{
				df++;
				
				StringTokenizer tokenArticle = new StringTokenizer (article);
				
				while (tokenArticle.hasMoreTokens())
				{
					
					currentTerm = tokenArticle.nextToken();
					currentTerm = currentTerm.toLowerCase();
					
					if (currentTerm.contentEquals(term.getTermString().toLowerCase()))
					{
						tf++;
						positionsTerm.add(position);
						
					}
					
					if (queryTerms.contains(currentTerm.toLowerCase()))
					{
						positionsQueryTerms.add(position);
					}
					
					position++;
				}
				
				pairCoOccurr = calculatePairCoOcurr (positionsQueryTerms,positionsTerm);
				while (i<positionsQueryTerms.size() && j<positionsTerm.size())
				{
					if (positionsQueryTerms.get(i) <= positionsTerm.get(j))
					{
						
						distance = Math.abs(positionsQueryTerms.get(i) - positionsTerm.get(j));
						if (distance <= windowSize)
							coOcurr++;
						i++;
						
					}
					else
					{
						distance = Math.abs(positionsQueryTerms.get(i) - positionsTerm.get(j));
						if (distance <= windowSize)
							coOcurr++;
						
						j++;
					}
						
					if (distance <= generalWindowSize)	
						withinWindowSize = true;
				}
				
				break;
			}
		}
		
		if (withinWindowSize)		
			termProx++;
		
	}
}
