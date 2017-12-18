package de.l3s.souza.word2vecseedfinder;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.net.MalformedURLException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.twelvemonkeys.imageio.metadata.exif.TIFF;

import ciir.umass.edu.eval.Evaluator;
import ciir.umass.edu.features.ZScoreNormalizor;
import ciir.umass.edu.learning.RANKER_TYPE;
import ciir.umass.edu.metric.METRIC;

import java.util.StringTokenizer;
import java.util.Vector;

import de.l3s.souza.esfive.Article;
import de.l3s.souza.esfive.LivingKnowledgeSnapshot;
import de.l3s.souza.date.DateUtils;
import de.l3s.souza.evaluation.DocumentParser;
import de.l3s.souza.evaluation.DocumentSimilarity;
import de.l3s.souza.evaluation.LivingKnowledgeEvaluation;
import de.l3s.souza.evaluation.PairDocumentSimilarity;
import de.l3s.souza.learningtorank.Term;
import de.l3s.souza.learningtorank.TermUtils;
import de.l3s.souza.preprocess.PreProcess;
import de.unihd.dbs.heideltime.standalone.HeidelTimeStandalone;

public class QueryExpansion {
	
	private HashMap<String,Double> queryCandidatesScores;
	
	private HashMap<String, Double> candidateQueries;
	private Term termL2r = new Term ("");
	private Evaluator l2rEvaluator;
	private HashSet<String> usedQueries;
	private String aQuery;
	private StringBuilder featuresVectors = new StringBuilder ();
	private HashMap<String,String> unlabeledDocs;
	private String eventDate;
	private int maxFreqUsedTerm;
	private DateUtils dateUtils = new DateUtils ();
	private PairDocumentSimilarity parser = new PairDocumentSimilarity ();
	private HashSet <String> collectionSpecification;
	private HashMap<String,Double> urlTerms = new HashMap<String,Double>(); //to hold all terms
	private HashMap<String,Double> usedTerms;
	private HashMap<String,Integer> termsUsedFreq;
	private DocumentSimilarity similarity;
	private HashMap<String,Double> querySimilarTerms;
	private HashSet<String> relevantDocuments;
	private HashMap<String,Article> articlesWithoutDup;
	private LivingKnowledgeEvaluation LivingKnowledgeEvaluator;
	private double beta;
	private boolean L2r;
	private int candidateTerms;
	private String topicID;
	private double alpha;
	private int expandTerms;
	private PreProcess preprocess;
	private static boolean ASC = true;
    private static boolean DESC = false;
	private int totalSimilar;
	HashMap<LivingKnowledgeSnapshot, Double> articles;
	private String currentQuery;
	private HashSet<String> nextQuery;
	private TermUtils termUtils;
	private HashMap<String,String> collection;
	
	public HashSet<String> getCollectionSpecification() {
		return collectionSpecification;
	}

	

	public boolean isL2r() {
		return L2r;
	}



	public void setL2r(boolean l2r) {
		L2r = l2r;
	}



	public void setCollectionSpecification(HashSet<String> collectionSpecification) {
		this.collectionSpecification = collectionSpecification;
	}


	public HashSet<String> getNextQuery() {
		return nextQuery;
	}

	public HashMap<String, Double> getUrlTerms() {
		return urlTerms;
	}

	public double getAvPrecision ()
	{
		return LivingKnowledgeEvaluator.getAvPrecision();
	}
	
	private void setCollection () throws IOException, Exception
	{
		collection = termUtils.getCollection();
	}
	public QueryExpansion (int maxSimTerms, String topicID, HashMap<LivingKnowledgeSnapshot,Double> articles,PreProcess preprocess) throws IOException
	{
		
		this.topicID = topicID;
		this.preprocess=preprocess;
		LivingKnowledgeEvaluator = new LivingKnowledgeEvaluation (topicID);
		this.articles = articles;
		LivingKnowledgeEvaluator.classifyDocuments(articles);
		relevantDocuments = new HashSet<String>();
	}
	public QueryExpansion(PreProcess preprocess,TermUtils termUtils,int maxUsedFreqTerm, String topicID,String cQuery,String aQuery, HashMap<String,Article> articlesWitDup,HashMap<LivingKnowledgeSnapshot,Double> art,
			int totalSimilar,int candidateTerms,int expandedTerms, String eventDate, double alpha,double beta,boolean L2r) throws Exception {
		
		candidateQueries = new HashMap<String,Double>();
		usedQueries = new HashSet<String>();
		queryCandidatesScores = new HashMap<String,Double>();
		this.candidateTerms = candidateTerms;
		this.termUtils = termUtils;
		collection = new HashMap<String,String>();
		setCollection();
		this.L2r=L2r;
		l2rEvaluator = new Evaluator (RANKER_TYPE.LAMBDAMART,METRIC.MAP,METRIC.MAP);
		l2rEvaluator.normalize = true;
		l2rEvaluator.nml = new ZScoreNormalizor();
		this.aQuery = aQuery;
		maxFreqUsedTerm = maxUsedFreqTerm;
		this.eventDate = eventDate;
		this.topicID = topicID;
		LivingKnowledgeEvaluator = new LivingKnowledgeEvaluation (topicID);
		relevantDocuments = new HashSet<String>();
		unlabeledDocs = new HashMap<String,String>();
		this.preprocess = preprocess;
		currentQuery = cQuery;
		nextQuery = new HashSet<String>();
		queryCandidatesScores = new HashMap<String,Double>();
		usedTerms = new HashMap<String,Double>();
		termsUsedFreq = new HashMap<String,Integer>();
		querySimilarTerms = new HashMap<String,Double>();
		articlesWithoutDup = new HashMap<String,Article>();
		
		setArticlesWithoutDup (articlesWitDup);
		articles = new HashMap<LivingKnowledgeSnapshot,Double>(art);
		this.alpha = alpha;
		this.beta = beta;
		this.totalSimilar = totalSimilar;
		expandTerms = expandedTerms;
	}

	
	public HashMap<String, Article> getArticlesWithoutDup() {
		return articlesWithoutDup;
	}
	
	public HashMap<LivingKnowledgeSnapshot, Double> getArticles() {
		return articles;
	}

	public void setArticles(HashMap<LivingKnowledgeSnapshot, Double> articles) {
		this.articles = articles;
	}

	public void setArticlesWithoutDup(HashMap<String, Article> newArticleSet) {
		articlesWithoutDup.clear();
		articlesWithoutDup = new HashMap<String,Article>(newArticleSet);
		
		for (Entry<String, Article> s : articlesWithoutDup.entrySet())	
		{
			unlabeledDocs.put(s.getValue().getText(), "1");
			
		}
	}

	public double getBeta() {
		return beta;
	}

	public void setBeta(double beta) {
		this.beta = beta;
	}

	public double getAlpha() {
		return alpha;
	}

	public void setAlpha(double alpha) {
		this.alpha = alpha;
	}

	public int getTotalSimilar() {
		return totalSimilar;
	}

	public void setTotalSimilar(int totalSimilar) {
		this.totalSimilar = totalSimilar;
	}

	public String getCurrentQuery() {
		return currentQuery;
	}

	public void setCurrentQuery(String currentQuery) {
		this.currentQuery = currentQuery;
	}

	public void resetQueryExpansionTerms ()
	{
		querySimilarTerms.clear();
		queryCandidatesScores.clear();
		nextQuery.clear();
	}
	
	public LivingKnowledgeEvaluation getLivingKnowledgeEvaluator() {
		return LivingKnowledgeEvaluator;
	}

	public void extractSimilarTermsUrls (deepLearningUtils deepLearning,double gama) throws Exception
	{
		int count = 0;
		int count2 = 0;
		String timeRetrieved;
		Date d1 = new Date ();
		String[] allMatches;
		HashMap<String,Double> classifiedDocuments = new HashMap<String,Double>();
		nextQuery.clear();
		urlTerms.clear();
		
		int pseudoRelv = 0;
		for (Entry<LivingKnowledgeSnapshot, Double> s : articles.entrySet())	
		{
			
			timeRetrieved = null;
			
			pseudoRelv ++;
			classifiedDocuments = LivingKnowledgeEvaluator.classifyDocuments(articles);
			double relevance = classifiedDocuments.get(s.getKey().getDocId());
			
			/*if (pseudoRelv > 20)
				break;*/
			if ((relevance>0))
				//continue;
			//else
				relevantDocuments.add(s.getKey().getDocId());
			else
				continue;
			allMatches = null;
			String url = s.getKey().getUrl();
			allMatches = dateUtils.getDate(url);
			
			if (allMatches[0] != null)
			{
				
				//double newSim = calculateTempScoreTerm (allMatches[0],relevance);
				
				urlTerms.put(allMatches[0],(double) 1);
				
			}
				
			String tokenizedTerms = preprocess.preProcessUrl(url);   //to get individual terms
			if (tokenizedTerms.contentEquals(""))
				continue;
			
			StringTokenizer token = new StringTokenizer (tokenizedTerms);
			
			while (token.hasMoreTokens()) {
				String term = token.nextToken();
				term = term.toLowerCase();
				Collection<String> nearest = deepLearning.getWordsNearest(term, 1);
				timeRetrieved = null;
				
				if (term.length()<=2)
					continue;
			
				if (!nearest.isEmpty())
					urlTerms.put(term, relevance);
					
			}	
			
		}
		
		System.out.println ("articles: "+articles.size()+ " relevant so far "+ relevantDocuments.size());
		
		if (relevantDocuments.size()==0)
		{
			StringTokenizer tokenaQuery = new StringTokenizer (aQuery);
			while (tokenaQuery.hasMoreTokens())
			{
				nextQuery.add(tokenaQuery.nextToken());
			}
		}
		
		if (L2r)
		{
			updateFeaturesVectors ();
			String ranked = l2rEvaluator.rankToString("/home/souza/mymodels/f3.cas", featuresVectors.toString());
			reScoreTermsL2R (ranked);
		}	
			//System.out.println(ranked);
			
		if (!L2r)
	        urlTerms = normalizeScores (urlTerms);
		
		
	/*	for (Entry<String,Double> s: urlTerms.entrySet())
		{
			
			String candidate = s.getKey();
			StringTokenizer token = new StringTokenizer (currentQuery);
			
			double sim = 0;
			
			while (token.hasMoreTokens())
				sim = sim + deepLearning.getCosSimilarity(token.nextToken(), candidate);
			
			if (sim < 0)
				sim = 0.0f;
			
			sim /= currentQuery.length();
			
			double finalScore = (gama*sim) + (1-gama)*s.getValue();
			
			urlTerms.put(s.getKey(), finalScore);
		}
		*/
		
		Map<String, Double> ordered = sortByComparator (urlTerms,DESC);
		int terms = 0;
		for (Entry<String, Double> s : ordered.entrySet())
		{
			int value = 0;
			if (termsUsedFreq.containsKey(s.getKey()))
				value = termsUsedFreq.get(s.getKey());
			else
				termsUsedFreq.put(s.getKey(), value);
			
			if (terms <= expandTerms && value < maxFreqUsedTerm)
			{
				nextQuery.add(s.getKey());
				terms ++;
				termsUsedFreq.put(s.getKey(), value+1);
			}
		}
	/*	
		for (Entry<String,Double> s: urlTerms.entrySet())
		{
			System.out.println (s.getKey() + " " +s.getValue());
		}
		*/
		
		if (nextQuery.isEmpty())
		{
			StringTokenizer tokenaQuery = new StringTokenizer (aQuery);
			while (tokenaQuery.hasMoreTokens())
			{
				String current = tokenaQuery.nextToken();
				nextQuery.add(current);
				if (termsUsedFreq.containsKey(current))
				{
					int value = termsUsedFreq.get(current);
					termsUsedFreq.put(current, value+1);
				}
				else 
					termsUsedFreq.put(current,1);
			}
		}
			
	}
	
	
	public PreProcess getPreprocess() {
		return preprocess;
	}


	public void setPreprocess(PreProcess preprocess) {
		this.preprocess = preprocess;
	}


	public HashMap<String,Double> getCandidateTerms (deepLearningUtils deepLearning) throws Exception
	{
		int pseudoRelevantDoc = 0;
		
		urlTerms.clear();
		HashMap<String,Double> classifiedDocuments = new HashMap<String,Double>();

		for (Entry<LivingKnowledgeSnapshot, Double> s : articles.entrySet())	
		{
			pseudoRelevantDoc++;
			classifiedDocuments = LivingKnowledgeEvaluator.classifyDocuments(articles);
			double relevance = classifiedDocuments.get(s.getKey().getDocId());
			
			if (relevance > 0)
				relevantDocuments.add(s.getKey().getDocId());
			else
				continue;
			
			if (pseudoRelevantDoc > 100)
				break;
			StringTokenizer token = new StringTokenizer (s.getKey().getTemp(),",");
			String currentCandidateQuery = "";
			double currentScoreCandidateQuery = 0.0F;
			int termsCandidateQuery = 0;
			while (token.hasMoreTokens()) {
				String term = token.nextToken();
				term = term.toLowerCase();
			
				term = term.replaceAll(","," ");
				StringTokenizer tokenTerm = new StringTokenizer (term);
				
				while (tokenTerm.hasMoreTokens())
				{
					String currentTokenTerm = tokenTerm.nextToken();
					currentTokenTerm = preprocess.removeNonLettersString(currentTokenTerm);
					
					
					if (currentTokenTerm.length()<=2)
						continue;
					
					if (preprocess.isStopWord(currentTokenTerm))
						continue;
					
					Collection<String> nearest = deepLearning.getWordsNearest(currentTokenTerm, 60);
				
					if (term.length()<=2)
						continue;
			
					if (!nearest.isEmpty())
					{
						
						Iterator<String> iteratorNearest = nearest.iterator();
						
						while (iteratorNearest.hasNext())
						{
						
							String currentNearest = iteratorNearest.next();
							double cos = deepLearning.getCosSimilarity(currentNearest, term);
							currentNearest = preprocess.removeNonLettersString(currentNearest);
							
							
							if (currentNearest.length()<=2)
								continue;
							
							if (preprocess.isStopWord(currentNearest))
								continue;
							
							
							urlTerms.put(currentNearest,cos);
						
						}
					}
				}
				
				
			}	
			
		}
		
		return urlTerms;
		
			
	}
	
	public void extractSimilarTermsText (deepLearningUtils deepLearning, boolean order) throws Exception
	{
		int pseudoRelevantDoc = 0;
		urlTerms.clear();
		int addedTerms=0;
		nextQuery.clear();
		int currentRelevant = 0;
		//featuresVectors = new StringBuilder ();
		String currentQuery = "";
		StringTokenizer tokenaQuery = new StringTokenizer (aQuery);
		/*while (tokenaQuery.hasMoreTokens())
		{
			String current = tokenaQuery.nextToken();
			nextQuery.add(current);
			if (tokenaQuery.hasMoreTokens())
				currentQuery = currentQuery + current + " ";
			else
				currentQuery = currentQuery + current;
		}*/
		
		//termUtils.setQuery(currentQuery);
		//urlTerms.clear();
		HashMap<String,Double> classifiedDocuments = new HashMap<String,Double>();

		for (Entry<LivingKnowledgeSnapshot, Double> s : articles.entrySet())	
		{
			pseudoRelevantDoc++;
			classifiedDocuments = LivingKnowledgeEvaluator.classifyDocuments(articles);
			double relevance = classifiedDocuments.get(s.getKey().getDocId());
			
			if (relevance > 0)
			{
				relevantDocuments.add(s.getKey().getDocId());
				currentRelevant++;
			}
		/*	else
				continue;
			
			/*if (pseudoRelevantDoc > 50)
				break;*/
			StringTokenizer token = new StringTokenizer (s.getKey().getTemp(),",");
			
			while (token.hasMoreTokens()) {
				String term = token.nextToken();
				term = term.toLowerCase();
				term = term.replaceAll(","," ");
				StringTokenizer tokenTerm = new StringTokenizer (term);
				
				while (tokenTerm.hasMoreTokens())
				{
					String currentTokenTerm = tokenTerm.nextToken();
					
					currentTokenTerm = preprocess.removeNonLettersString(currentTokenTerm);
					
					if (preprocess.isStopWord(currentTokenTerm))
						continue;
					
					if (currentTokenTerm.length()<=2)
						continue;
					
					Collection<String> nearest = deepLearning.getWordsNearest(currentTokenTerm, totalSimilar);
				
					if (term.length()<=2)
						continue;
			
					if (!nearest.isEmpty())
					{
						
						Iterator<String> iteratorNearest = nearest.iterator();
						
						while (iteratorNearest.hasNext())
						{
							
							String currentNearest = iteratorNearest.next();
							
							currentNearest = preprocess.removeNonLettersString(currentNearest);
							if (currentNearest.length()<=2)
								continue;
							double cos = deepLearning.getCosSimilarity(currentNearest, term);
							//if (urlTerms.size() < candidateTerms)
							if (addedTerms < candidateTerms)
							{
								urlTerms.put(currentNearest,cos);
								addedTerms++;
							}
							else
								break;
							//updateFeaturesVectors (currentNearest);
						/*	if (termsCandidateQuery<expandTerms)
							{
								currentCandidateQuery += " " + currentNearest;
								currentScoreCandidateQuery += cos;
								termsCandidateQuery++;
							}*/
						}
					}
					
					//if (urlTerms.size() > candidateTerms)
					if (addedTerms > candidateTerms)
						break;
				}
				if (addedTerms > candidateTerms)
				//if (urlTerms.size() > candidateTerms)
					break;
			}
			/*
			addedTerms=0;
			
			StringTokenizer tokenTitle = new StringTokenizer (s.getKey().getTitle());
			while (tokenTitle.hasMoreTokens())
			{
				String currentTokenTerm = tokenTitle.nextToken();
				if (preprocess.isStopWord(currentTokenTerm))
					continue;
				Collection<String> nearest = deepLearning.getWordsNearest(currentTokenTerm, totalSimilar);
			
				if (currentTokenTerm.length()<=2)
					continue;
		
				if (!nearest.isEmpty())
				{
					
					Iterator<String> iteratorNearest = nearest.iterator();
					
					while (iteratorNearest.hasNext())
					{
					
						String currentNearest = iteratorNearest.next();
						currentNearest = preprocess.removeNonLettersString(currentNearest);
						
						if (currentNearest.length()<=2)
							continue;
						
						double cos = deepLearning.getCosSimilarity(currentNearest, currentTokenTerm);
						
						
						if (addedTerms < candidateTerms/2)
						{
							urlTerms.put(currentNearest,cos);
							addedTerms++;
						}
						else
							break;
						//updateFeaturesVectors (currentNearest);
					/*	if (termsCandidateQuery<expandTerms)
						{
							currentCandidateQuery += " " + currentNearest;
							currentScoreCandidateQuery += cos;
							termsCandidateQuery++;
						}
					}
				}
				
				if (addedTerms > candidateTerms/2)
					break;
			}
			
			
			String tokenizedTerms = preprocess.preProcessUrl(s.getKey().getUrl());   //to get individual terms
			if (tokenizedTerms.contentEquals(""))
				continue;
			
			StringTokenizer tokenUrl = new StringTokenizer (tokenizedTerms);
			
			while (tokenUrl.hasMoreTokens()) {
				String term = tokenUrl.nextToken();
				term = term.toLowerCase();
				Collection<String> nearest = deepLearning.getWordsNearest(term, totalSimilar);
				
				if (term.length()<=2)
					continue;
			
				if (!nearest.isEmpty())
				{
					
					if (addedTerms < candidateTerms/2)
					{
						urlTerms.put(term, relevance);
						addedTerms++;
					}
					else
						break;
					
				//	updateFeaturesVectors (term);
				}	
				
				if (addedTerms > candidateTerms/2)
					break;
			}	
			/*if (termsCandidateQuery>0)
				candidateQueries.put(currentCandidateQuery, currentScoreCandidateQuery/termsCandidateQuery);
			*/
			
		}
		
	/*	if (currentRelevant == 0)
		{
			extractSimilarTermsQuery (deepLearning, this.currentQuery) ;
			return;
		}
		*/
	if (L2r)
	{
		updateFeaturesVectors ();
		String ranked = l2rEvaluator.rankToString("/home/souza/mymodels/f3.cas", featuresVectors.toString());
		reScoreTermsL2R (ranked);
	}	
		//System.out.println(ranked);
		
	if (!L2r)
        urlTerms = normalizeScores (urlTerms);
		
		System.out.println ("articles: "+articles.size()+ " relevant so far "+ relevantDocuments.size());
		
		Map<String, Double> ordered = sortByComparator (urlTerms,order);
		int terms = 0;
		for (Entry<String, Double> s : ordered.entrySet())
		{
			int value = 0;
			if (termsUsedFreq.containsKey(s.getKey()))
				value = termsUsedFreq.get(s.getKey());
			else
				termsUsedFreq.put(s.getKey(), value);
			
			if (terms <= expandTerms && value < maxFreqUsedTerm)
			{
				nextQuery.add(s.getKey());
				terms ++;
				termsUsedFreq.put(s.getKey(), value+1);
			}
		}
			
	}
	
	
	public double calculateTempScoreTerm (String date, double termScore)
	{
		
		Date timeC = null, timeQ = null;
		double relevanceScore;
		double tempBasedScore;
		
		SimpleDateFormat ft = new SimpleDateFormat ("yyyy-dd-MM");
		
		if (date.length()<=4)
			date = date + "-01-01";
		else
			date = date.replaceAll("/", "-");
		try {
	         timeC = ft.parse(date); 
	         timeQ = ft.parse(eventDate);
	      }catch (Exception e) { 
	         return 0.0f; 
	      }

		
		long diff = timeC.getTime() - timeQ.getTime();
		
		if (diff==0)
		{
			relevanceScore = alpha * termScore + (1-alpha);
		}
		else
		{
			
			tempBasedScore = (double)1/Math.abs(diff);
			relevanceScore = alpha * termScore + (1-alpha)*tempBasedScore;
		}
		
		return relevanceScore;

	}
	public String extractSimilarTermsQuery (deepLearningUtils deepLearning, String query) throws Exception
	{
		String currentTerm;
		String newQuery = "";
		StringTokenizer token = new StringTokenizer (query);
		resetQueryExpansionTerms();
		urlTerms = new HashMap<String,Double> ();
		nextQuery.clear();
		featuresVectors = new StringBuilder ();
		while (token.hasMoreTokens())
		{
			currentTerm = token.nextToken();
			Collection<String> nearest = deepLearning.getWordsNearest(currentTerm, totalSimilar);
			
			  for (Iterator iterator = nearest.iterator(); iterator.hasNext();) 
			  {
			        String element = (String) iterator.next();
			        urlTerms.put(element, 1.0);

			  }
			
		}
		
	/*	for (Entry<String, Double> s : urlTerms.entrySet())	
		{
			token = new StringTokenizer (query);
		
			currentTerm = s.getKey();
			double sim = 0;
			
			while (token.hasMoreTokens())
			{
				sim = sim + deepLearning.getCosSimilarity(token.nextToken(), currentTerm);
				if (sim > 1)
				{
					sim = 1;
				}
			}
			
			urlTerms.put(currentTerm,sim);
		}
		*/
		if (L2r)
		{
			updateFeaturesVectors ();
			String ranked = l2rEvaluator.rankToString("/home/souza/mymodels/f3.cas", featuresVectors.toString());
			reScoreTermsL2R (ranked);
		}	
			//System.out.println(ranked);
			
		if (!L2r)
	        urlTerms = normalizeScores (urlTerms);
		//calculateScores(deepLearning);
		//querySimilarTerms = normalizeScores (querySimilarTerms);
		
		Map<String, Double> ordered = sortByComparator (querySimilarTerms,DESC);
		int terms = 0;
		for (Entry<String, Double> s : ordered.entrySet())
		{
			int value = 0;
			if (termsUsedFreq.containsKey(s.getKey()))
				value = termsUsedFreq.get(s.getKey());
			else
				termsUsedFreq.put(s.getKey(), value);
			
			if (terms <= expandTerms && value < maxFreqUsedTerm)
			{
				newQuery += " " + s.getKey();
				terms ++;
				termsUsedFreq.put(s.getKey(), value+1);
				nextQuery.add(s.getKey());

			}
		}
		
		return newQuery;
	}
	
	public String extractSimilarTermsQuery (deepLearningUtils deepLearning, String query, int pos) throws Exception
	{
		String currentTerm;
		String newQuery = "";
		int i = 0;
		StringTokenizer token = new StringTokenizer (query);
		resetQueryExpansionTerms();
		urlTerms = new HashMap<String,Double> ();
		nextQuery.clear();
		featuresVectors = new StringBuilder ();
		while (token.hasMoreTokens())
		{

			if (i>pos)
				break;
			
			if (i!=pos)
			{
				currentTerm = token.nextToken();
				i++;
				continue;
			}
			else	
				currentTerm = token.nextToken();
			
			Collection<String> nearest = deepLearning.getWordsNearest(currentTerm, totalSimilar);
			
			  for (Iterator iterator = nearest.iterator(); iterator.hasNext();) 
			  {
			        String element = (String) iterator.next();
			        urlTerms.put(element, 1.0);

			  }
			  i++;
				
		}
		
	/*	for (Entry<String, Double> s : urlTerms.entrySet())	
		{
			token = new StringTokenizer (query);
		
			currentTerm = s.getKey();
			double sim = 0;
			
			while (token.hasMoreTokens())
			{
				sim = sim + deepLearning.getCosSimilarity(token.nextToken(), currentTerm);
				if (sim > 1)
				{
					sim = 1;
				}
			}
			
			urlTerms.put(currentTerm,sim);
		}
		*/
		if (L2r)
		{
			updateFeaturesVectors ();
			String ranked = l2rEvaluator.rankToString("/home/souza/mymodels/f3.cas", featuresVectors.toString());
			reScoreTermsL2R (ranked);
		}	
			//System.out.println(ranked);
			
		if (!L2r)
	        urlTerms = normalizeScores (urlTerms);
		//calculateScores(deepLearning);
		//querySimilarTerms = normalizeScores (querySimilarTerms);
		
		Map<String, Double> ordered = sortByComparator (querySimilarTerms,DESC);
		int terms = 0;
		for (Entry<String, Double> s : ordered.entrySet())
		{
			int value = 0;
			if (termsUsedFreq.containsKey(s.getKey()))
				value = termsUsedFreq.get(s.getKey());
			else
				termsUsedFreq.put(s.getKey(), value);
			
			if (terms <= expandTerms && value < maxFreqUsedTerm)
			{
				newQuery += " " + s.getKey();
				terms ++;
				termsUsedFreq.put(s.getKey(), value+1);
				nextQuery.add(s.getKey());

			}
		}
		
		return newQuery;
	}
	
	private void calculateScores ( deepLearningUtils deepLearning) {
		
		 int sumTermFrequency;
		
		  if (!querySimilarTerms.isEmpty())
		  {
			for (Entry<String, Double> s : querySimilarTerms.entrySet())
			{
				sumTermFrequency = 0;
				String currentTerm = s.getKey();
				double score = 0.0f;
				
				for(Entry<String, Article> s2 : articlesWithoutDup.entrySet())
				{
					int termFrequency = getTermFrequency(s2.getValue().getText(),currentTerm);
					sumTermFrequency = sumTermFrequency + termFrequency;
				}
				
					score = (sumTermFrequency*alpha) + (1-alpha)*s.getValue();
					
					querySimilarTerms.put(currentTerm, score);
					queryCandidatesScores.put(currentTerm, score);
			}
		  }
		  calculateScoresQueryTerms(totalSimilar,deepLearning);
	}
	
	
	//softmax normalization
	private HashMap<String,Double> normalizeScores (HashMap<String,Double> origin)
	{
		HashMap<String,Double> result = new HashMap<String,Double>();
		double sumExp=0;
		for (Entry<String,Double>  s : origin.entrySet() )
			sumExp = sumExp + Math.exp(s.getValue());
		
		for (Entry<String,Double>  s : origin.entrySet() )
		{
			double normalizedScore = Math.exp(s.getValue())/sumExp;
			result.put(s.getKey(), normalizedScore);
		}
		
		return result;
	}
	
	public HashMap<String,Double> getNewScoreEntities (deepLearningUtils deepLearning,HashMap<String,Double> entities)
	{
		HashMap<String,Double> entitiesOutput = new HashMap<String,Double>();
		
		for (Entry<String, Double> s : entities.entrySet())
		{
			if (queryCandidatesScores.containsKey(s.getKey()))
				continue;
				
				StringTokenizer token = new StringTokenizer (currentQuery);
			
				String currentTerm = s.getKey();
				double sum = 0;
				while (token.hasMoreTokens())
				{
					double sim;
					sim = deepLearning.getCosSimilarity(token.nextToken(), currentTerm);
					sum = sum + sim;
				}
				
				
				sum = sum/currentQuery.length();
				entitiesOutput.put(currentTerm, sum);

		}
		return entitiesOutput;
		
	}
	public int getTermFrequency (String document, String term)
	{
		int frequency = 0;
		String current = " ";
		StringTokenizer token = new StringTokenizer (document);
		
		while (token.hasMoreTokens())
		{
			current = token.nextToken().toLowerCase();
			if (current.contentEquals(term))
				frequency++;
		}
		return frequency;
		
	}
	
	private void calculateScoresQueryTerms (int totalSimilar,deepLearningUtils deepLearning)
	{
			HashSet<String> domains = new HashSet<String>();
			HashSet<String> years = new HashSet<String>();
			HashSet<String> languages = new HashSet<String>();
			double sim;
			double currentScore;
			String element = null;
			
			for(Entry<LivingKnowledgeSnapshot, Double> s : articles.entrySet())
			{
				String domain = s.getKey().getHost();
				domains.add(domain);
			//	annotations.setLanguage(s.getValue().getText());
			//	Vector<String> language = annotations.getLanguage();
			//	languages.add(language.firstElement());
				years.add(s.getKey().getDate().substring(0, 3));
			}
			
			StringTokenizer token = new StringTokenizer (currentQuery);
			
			while (token.hasMoreTokens())
			{
				String currentQueryTerm = token.nextToken();
				
				Collection<String> similarTerms = deepLearning.getWordsNearest(currentQueryTerm, totalSimilar);
				
				 for (Iterator iterator = similarTerms.iterator(); iterator.hasNext();) 
				 {
				        element = (String) iterator.next();
				        break;
				 }
				 
			 if (element!=null)	 
				sim = deepLearning.getCosSimilarity(currentQueryTerm, element);
			 else
				sim = 0;
			 
			 currentScore = beta *(domains.size() + languages.size() + years.size()+ sim);
			
			 usedTerms.put(currentQueryTerm, currentScore);
			 queryCandidatesScores.put(currentQueryTerm, currentScore);
			}
			
			Map<String, Double> ordered = sortByComparator (queryCandidatesScores,DESC);
			int terms = 0;
			for (Entry<String, Double> s : ordered.entrySet())
			{
				terms ++;
				if (terms <= expandTerms)
					nextQuery.add(s.getKey());
			}
			
	}
	
	private static Map<String, Double> sortByComparator(Map<String, Double> unsortMap, final boolean order)
	{

	            List<Entry<String, Double>> list = new LinkedList<Entry<String, Double>>(unsortMap.entrySet());

	            // Sorting the list based on values
	            Collections.sort(list, new Comparator<Entry<String, Double>>()
	            {
	                public int compare(Entry<String, Double> o1,
	                        Entry<String, Double> o2)
	                {
	                    if (order)
	                    {
	                        return o1.getValue().compareTo(o2.getValue());
	                    }
	                    else
	                    {
	                        return o2.getValue().compareTo(o1.getValue());

	                    }
	                }
	            });

	            // Maintaining insertion order with the help of LinkedList
	            Map<String, Double> sortedMap = new LinkedHashMap<String, Double>();
	            for (Entry<String, Double> entry : list)
	            {
	                sortedMap.put(entry.getKey(), entry.getValue());
	            }

	            return sortedMap;
	}
	
    public void parseFiles(String filePath) throws FileNotFoundException, IOException {
        File[] allfiles = new File(filePath).listFiles();
        BufferedReader in = null;
        int i = 0;
        int size = allfiles.length;
        String filteredDocument="";
        
        for (File f : allfiles) {
            if (f.getName().endsWith(".txt")) {
                in = new BufferedReader(new FileReader(f));
                StringBuilder sb = new StringBuilder();
                String s = null;
                while ((s = in.readLine()) != null) {
                    sb.append(s);
                }
                
                filteredDocument = preprocess.removeStopWords(sb.toString());
                collectionSpecification.add(filteredDocument);
            }
        }
    }
    
    public void reScoreTermsL2R (String rankedL2r)
    {
    	urlTerms.clear();
    	StringTokenizer token = new StringTokenizer (rankedL2r);
    	String term;
   		double score;
    		while (token.hasMoreTokens())
    		{
    			try {
    			term = token.nextToken();
    		//	score = Math.abs(Double.parseDouble(token.nextToken()));
    			score =Double.parseDouble(token.nextToken());
    			urlTerms.put(term, score);
    			} catch (Exception e)
    			{
    				
    			}
    		}
	}
    
    public void updateFeaturesVectors (String currentTerm) throws Exception
    {
    	Term termL2r = new Term (currentTerm);
		termUtils.setTerm(termL2r);
		termUtils.calculateFeaturesCollectionOnline(collection);
		termUtils.calculateFeaturesOnline(articles,preprocess);
		
		HashMap<Integer,Double> features = new HashMap<Integer,Double>();
		features = termL2r.getFeaturesVector();
		featuresVectors.append("0 "+"qid:"+topicID+" ");
		int indice = 0;
		
		for (Entry<Integer,Double> feature : features.entrySet())
		{
			if (indice<=features.size())
				featuresVectors.append(feature.getKey()+":"+feature.getValue() + " ");
			else
				featuresVectors.append(feature.getKey()+":"+feature.getValue());
			indice++;
			
		}
			
		featuresVectors.append(" #"+termL2r.getTermString()+"\n");
    }
	
    
    public void updateFeaturesVectors () throws Exception
    {
    	int i = 0;
    	for (Entry<String, Double> s : urlTerms.entrySet())
		{
    	
    		i++;
    		if (featuresVectors.toString().contains(s.getKey()))
    			continue;
    	termL2r.setTermString(s.getKey());
		termUtils.setTerm(termL2r);
		termUtils.calculateFeaturesCollectionOnline(collection);
		termUtils.calculateFeaturesOnline(articles,preprocess);
		
		HashMap<Integer,Double> features = new HashMap<Integer,Double>();
		features = termL2r.getFeaturesVector();
		featuresVectors.append("0 "+"qid:"+topicID+" ");
		int indice = 0;
		
		for (Entry<Integer,Double> feature : features.entrySet())
		{
			if (indice<=features.size())
				featuresVectors.append(feature.getKey()+":"+feature.getValue() + " ");
			else
				featuresVectors.append(feature.getKey()+":"+feature.getValue());
			indice++;
		}
			
		featuresVectors.append(" # "+termL2r.getTermString()+"\n");
		
		}
    }
}
