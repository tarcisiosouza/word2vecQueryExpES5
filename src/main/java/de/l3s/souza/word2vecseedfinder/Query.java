package de.l3s.souza.word2vecseedfinder;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Files;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.StringTokenizer;

import de.l3s.souza.esfive.Article;
import de.l3s.souza.esfive.ElasticMain;
import de.l3s.souza.esfive.LivingKnowledgeSnapshot;
import de.l3s.souza.evaluation.LivingKnowledgeEvaluation;
import de.l3s.souza.evaluation.PairDocumentSimilarity;
import de.l3s.souza.evaluation.ScoreFunctions;
import de.l3s.souza.learningtorank.TermUtils;
import de.l3s.souza.output.HtmlOutput;
import de.l3s.souza.preprocess.PreProcess;
import de.unihd.dbs.heideltime.standalone.DocumentType;
import de.unihd.dbs.heideltime.standalone.HeidelTimeStandalone;
import de.unihd.dbs.heideltime.standalone.OutputType;
import de.unihd.dbs.heideltime.standalone.POSTagger;
import de.unihd.dbs.heideltime.standalone.exceptions.DocumentCreationTimeMissingException;
import de.unihd.dbs.uima.annotator.heideltime.resources.Language;

public class Query 
{
	private static final boolean localmode = false;
	private PreProcess preprocess;
	private ScoreFunctions urlScoreObject;
	private HashMap<StringBuilder,Double> sbResults = new HashMap<StringBuilder,Double> ();
	private HashMap<StringBuilder,Double> sbRes = new HashMap<StringBuilder,Double> ();
	private HashSet<String> usedQueries = new HashSet<String>();
	private int terms;
	private ElasticMain elasticUtil;
	private double alpha;
	private double gama;
	private double scoreParam;
	private double precisionAt20;
	private BufferedWriter bw;
	private int maxSimTerms;
	private int maxIter;
	private double bestMAP = 0.0;
	private String bestQuery;
	private int candidateTerms;
	private double nDCG;
	private LivingKnowledgeEvaluation evaluator;
	private String runname;
	private static HeidelTimeStandalone heidelTime;
	private int maxDoc;
	private static HashMap <String,String> urls = new HashMap<String,String>();
	private static ArrayList<String> vowels;
	private String currentQuery;
	private static StringBuilder sb = new StringBuilder();
	private String nextQuery;
	private HashMap<String, Article> articlesWithoutDuplicates;
	private HashMap<LivingKnowledgeSnapshot, Double> articles;
	private HashMap<String,Integer> queryTerms;
	private deepLearningUtils deepLearning;
	private int maxUsedFreqTerm;
	private QueryExpansion queryExpansion;
	private HashMap<LivingKnowledgeSnapshot, Double> retrievedDocuments;
	private static HashSet<String> domains;
	private HashSet<String> similarTermsLinks;
	private double beta;
	private boolean L2r;
	private HashMap<LivingKnowledgeSnapshot, Double> finalDocSet;
	private HashSet<String> entitiesInLinks;
	private HashMap<String,Double> entitiesCandidates;
	private ArrayList<String> entitiesFromBabelFy;
	private String field;
	private String topic;
	private int limit;
	public HashMap<String, Article> getArticlesWithoutDuplicates() {
		return articlesWithoutDuplicates;
	}

	public void setArticlesWithoutDuplicates(
			HashMap<String, Article> articlesWithoutDuplicates) {
		this.articlesWithoutDuplicates = articlesWithoutDuplicates;
	}

	public String getCurrentQuery() {
		return currentQuery;
	}
	
	public void setCurrentQueryID (String query)
	{
		currentQuery = query;
	}
	public PreProcess getPreprocess() {
		return preprocess;
	}

	public void setCurrentQuery(String currentQuery) {
		this.currentQuery = currentQuery;
		currentQuery = preprocess.removeStopWords(currentQuery);
		currentQuery = preprocess.removePunctuation(currentQuery);
		this.currentQuery = currentQuery;
	}
	
	public int getTerms() {
		return terms;
	}

	public void setTerms(int terms) {
		this.terms = terms;
	}

	public int getMaxSimTerms() {
		return maxSimTerms;
	}

	public void setMaxSimTerms(int maxSimTerms) {
		this.maxSimTerms = maxSimTerms;
	}

	public int getMaxDoc() {
		return maxDoc;
	}

	public void setMaxDoc(int maxDoc) {
		this.maxDoc = maxDoc;
	}

	
	public String buildNextQuery () throws IOException
	{
		
		//extractSimilarTermsCurrentQuery (maxSimTerms);
	
		//Map<String, Double> ordered = sortByComparator (queryCandidatesScores,DESC);
		
		return nextQuery;
	}

	public Query(int totalDocuments,String field) throws Exception {
	
		preprocess = new PreProcess();
		elasticUtil = new ElasticMain ("",limit,field,"souza_livingknowledge");
		this.field=field;
		setLimit(totalDocuments);
	
		deepLearning = new deepLearningUtils ("articles.txt");
		
		articles = new HashMap<LivingKnowledgeSnapshot,Double>();
		
		
	}
	
	public String getTopic() {
		return topic;
	}

	
	public void setTopic(String topic) {
		this.topic = topic;
		deepLearning.loadModel("/home/souza/ntcir11_models/"+topic+".txt");
	}

	public void processCurrentQuery () throws Exception
	{
		processQuery(currentQuery,field,"0");
		queryExpansion = new QueryExpansion(maxSimTerms,topic,articles,preprocess);
	}
	
	public HashMap<LivingKnowledgeSnapshot, Double> getArticles() {
		return articles;
	}

	public double getAvPrecision ()
	{
		return queryExpansion.getAvPrecision();
	}
	public HashMap<String,Double> getCandidateTerms () throws Exception
	{
		
		return queryExpansion.getCandidateTerms(deepLearning);
	}
	//
	public Query(int maxUsedFreqTerm,String runname, int limit,String field,int terms, int maxSimTerms,
			int candidateTerms, int maxDoc, int maxIter, double alpha,double beta,double gama,double scoreParam,boolean L2r) throws Exception {
		
		super();
		preprocess = new PreProcess();
		this.limit = limit;
		elasticUtil = new ElasticMain ("",limit,field,"souza_livingknowledge_2");
		this.field=field;
		deepLearning = new deepLearningUtils ("articles.txt");
		//deepLearning.loadModel("/home/souza/Word2VecTrainSources/complete_corpus.txt");
		this.beta = beta;
		urlScoreObject = new ScoreFunctions (scoreParam);
		entitiesCandidates = new HashMap<String,Double>();
		this.terms = terms;
		this.maxSimTerms = maxSimTerms;
		this.maxDoc = maxDoc;
		this.maxUsedFreqTerm=maxUsedFreqTerm;
		this.runname=runname;
		this.candidateTerms=candidateTerms;
		this.maxIter=maxIter;
		this.alpha=alpha;
		this.beta=beta;
		this.gama=gama;
		this.scoreParam=scoreParam;
		this.L2r=L2r;
	}
	
	public double getnDCG() {
		return nDCG;
	}

	public void setnDCG(double nDCG) {
		this.nDCG = nDCG;
	}

	public void run (TermUtils termUtils,String topicID, String title, String initialQuery,String titlePlusDescription,
			String eventDate) throws Exception
	{
		/*boolean result = false;
		File fileToDelete = new File ("/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/"+topicID+"/"+topicID+"."+runname+".res");
		try {
			result = Files.deleteIfExists(fileToDelete.toPath());
		}
		catch (Exception e){
		
			System.out.println (result);
			}*/
		
		/*		BufferedWriter res = new BufferedWriter(new FileWriter("/home/souza/NTCIR-eval/ntcir12_Temporalia_taskdata/Evaluation Data/"+topicID+"/"+topicID+"."+runname+".res", true));
		*/
		BufferedWriter res = new BufferedWriter(new FileWriter("/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/"+topicID+"/"+topicID+"."+runname+".res", true));
		bw = new BufferedWriter(new FileWriter("output.txt", true));
		BufferedWriter out = new BufferedWriter
    		    (new OutputStreamWriter(new FileOutputStream("word2vecseedfinder.html"),"UTF-8"));
		
		
		  sb.append("<html>");
		    sb.append("<head>");
		    
		    sb.append("<title> SeedFinder"+ field +" search Results");
		    sb.append("</title>");
		    sb.append("<style>");
		    sb.append("table, th, td {");
		    sb.append("border: 1px solid black;");
		    sb.append("border-collapse: collapse;");
		    sb.append("}");				    
		    sb.append("th, td {");
		    sb.append(" padding: 5px;");
		    sb.append("}");
		    sb.append("</style>");
		    sb.append("</head>");
		    sb.append("<body><center><b>SeedFinder " + field +"-search</b></center>");
		    sb.append("<center><b>Parameters {alpha: "+ alpha + " beta: "+ beta +" gama: "+ gama+ " scoreFunction: "+scoreParam+"}</b></center>");
		  //  sb.append("<body><center><b>URL search</b></center>");
		    sb.append("<script>");
		    sb.append("var e = document.getElementById('parent')");
		    sb.append ("e.onmouseover = function() {");
		    sb.append("document.getElementById('popup').style.display = 'block'");
		    sb.append ("}");
		    sb.append("e.onmouseout = function() {");
		    sb.append("document.getElementById('popup').style.display = 'none';");
		    sb.append("}");
		    sb.append("</script>");
		vowels = new ArrayList<String>();
		   vowels.add("a");
	       vowels.add("e");
	       vowels.add("i");
	       vowels.add("o");
	       vowels.add("u");
		domains = new HashSet<String>();
		//initialQuery = preprocess.removeStopWords(initialQuery);
		//initialQuery = preprocess.removeDuplicates(initialQuery);
		initialQuery = preprocess.removePunctuation(initialQuery);
		title = preprocess.removeStopWords(title);
		title = preprocess.removePunctuation(title);
		title = preprocess.removeDuplicates(title);
		titlePlusDescription = preprocess.removeStopWords(titlePlusDescription);
		titlePlusDescription = preprocess.removePunctuation(titlePlusDescription);
		this.currentQuery = initialQuery;
		queryTerms = new HashMap<String,Integer>();
		retrievedDocuments = new HashMap<LivingKnowledgeSnapshot, Double>();
		similarTermsLinks = new HashSet<String>();
		//new ElasticMain (initialQuery,limit,field,"souza_livingknowledge");
		articlesWithoutDuplicates = new HashMap<String,Article>();
		articles = new HashMap<LivingKnowledgeSnapshot,Double>();
		finalDocSet = new HashMap<LivingKnowledgeSnapshot, Double>();
		addQueryTerms(initialQuery);
		
		System.out.println ("Processing query: "+initialQuery+" "+"iter: 0");
		processQuery(initialQuery,field,"0");
		usedQueries.add(initialQuery);
	//	handleDuplicates(articles,"0");
		
		queryExpansion = new QueryExpansion(preprocess,termUtils,maxUsedFreqTerm,topicID,initialQuery,titlePlusDescription ,articlesWithoutDuplicates, articles, 
				maxSimTerms, candidateTerms,terms,eventDate, alpha, beta,L2r);

		evaluator = queryExpansion.getLivingKnowledgeEvaluator();
		
		evaluator.classifyDocuments(articles);
		double precision = evaluator.getAvPrecision();
		if (precision>bestMAP)
		{
			bestMAP = precision;
			bestQuery =  initialQuery;
		}
		if (precision<=0)
		{
			processQuery(title,field,"0");
			evaluator.classifyDocuments(articles);
			precision = evaluator.getAvPrecision();
			if (precision>bestMAP)
			{
				bestMAP = precision;
				bestQuery = title;
			}
			usedQueries.add(title);
		}
		
		deepLearning.loadModel("/home/souza/ntcir11_models/"+topicID+".txt");
		
		System.out.println("precision: "+ precision + " totalRelevantPRF: "+ evaluator.getTotalRelevantPRF());
		HtmlOutput html = new HtmlOutput ();
		html.outputArticlesHtml(sb, articles, "0", evaluator,topicID,runname);
		
		sbResults.put(html.getSb(), precision);
		
		sbRes.put(html.getSbRes(), precision);
		
		populateRetrivedDocuments();
	/*
		if (field.contentEquals("url"))
			queryExpansion.extractSimilarTermsUrls(deepLearning,gama);
		else
			queryExpansion.extractSimilarTermsText(deepLearning,false);
		HashSet<String> nextQuery;
		nextQuery = queryExpansion.getNextQuery();
		
		
	*/
		//field = "text";
		String currentQueryString = null;
		int iter = maxIter+1;
		
		titlePlusDescription = preprocess.removePunctuation(titlePlusDescription);
		titlePlusDescription = preprocess.removeStopWords(titlePlusDescription);
		titlePlusDescription = preprocess.removeDuplicates(titlePlusDescription);
		title = preprocess.removePunctuation(title);
        title = preprocess.removeStopWords(title);
        title = preprocess.removeDuplicates(title);
		while (iter <= maxIter)
		{
			
	        currentQueryString = addTermsCurrentQuery(bestQuery + " ",nextQuery);

		        currentQueryString = preprocess.removePunctuation(currentQueryString);
		        currentQueryString = preprocess.removeStopWords(currentQueryString);
		        currentQueryString = preprocess.removeDuplicates(currentQueryString);
			
		        
		        
			if (usedQueries.contains(currentQueryString))
			{
				if (!usedQueries.contains(title))
				{
					currentQueryString = title;
					//queryExpansion.extractSimilarTermsText(deepLearning,false);
					//nextQuery = queryExpansion.getNextQuery();
					//currentQueryString = addTermsCurrentQuery(currentQueryString,nextQuery);	
				
				}
				else
					{
					
//						if (!usedQueries.contains(titlePlusDescription))
	//					{
						//	currentQueryString = titlePlusDescription;
							currentQueryString = currentQueryString + " " + queryExpansion.extractSimilarTermsQuery(deepLearning, currentQueryString);

							if (usedQueries.contains(currentQueryString))
							{
								if (!currentQueryString.contentEquals(bestQuery))
									currentQueryString = addTermsBestQuery (currentQueryString);
								else
									currentQueryString = currentQueryString + " " + queryExpansion.extractSimilarTermsQuery(deepLearning, currentQueryString);
							/*	
								int size = currentQueryString.length();
								int position = 0;
								while (usedQueries.contains(currentQueryString))
								{
									
									if (position>size)
										break;
									
									currentQueryString = currentQueryString + " " + queryExpansion.extractSimilarTermsQuery(deepLearning, currentQueryString,position);
									position++;
								}*/	
								
							}
							//	queryExpansion.extractSimilarTermsText(deepLearning,false);
						//	nextQuery = queryExpansion.getNextQuery();
						//	currentQueryString = addTermsCurrentQuery(currentQueryString,nextQuery);
							
		//				}
			//				else
				//		{
							//	currentQueryString = currentQueryString + " " + queryExpansion.extractSimilarTermsQuery(deepLearning, currentQueryString);
					//	
						//}
					}
			}
			
			
			System.out.println ("Processing query: "+currentQueryString+" "+"iter: "+iter);
			addQueryTerms(currentQueryString);
			
			processQuery(currentQueryString,field,Integer.toString(iter));
				
			usedQueries.add(currentQueryString);
		//	articles = urlScoreObject.urlScoreFunction(heidelTime,deepLearning,topicID, eventDate,articles,Integer.toString(iter),urls,initialQuery);
		//	if (iter==maxIter)
				handleDuplicates(articles,Integer.toString(iter));
			
			articles = (HashMap<LivingKnowledgeSnapshot, Double>) sortByComparator(articles,false);
			
			html.outputArticlesHtml(sb, articles, Integer.toString(iter), evaluator,topicID,runname);
			populateRetrivedDocuments();
			evaluator.classifyDocuments(articles);
			precision = evaluator.getAvPrecision();
			
			if (precision>bestMAP)
			{
				bestMAP = precision;
				bestQuery = currentQueryString;
			}
			
			sbResults.put(html.getSb(), evaluator.getAvPrecision());
			sbRes.put(html.getSbRes(), evaluator.getAvPrecision());
			
			System.out.println("Precision: "+evaluator.getAvPrecision());
			queryExpansion.setCurrentQuery(currentQueryString);
			
			queryExpansion.setArticles(articles);
		
			queryExpansion.extractSimilarTermsText(deepLearning,false);
			nextQuery = queryExpansion.getNextQuery();
			currentQueryString = addTermsCurrentQuery(currentQueryString,nextQuery);
			//queryExpansion.extractSimilarTermsQuery(deepLearning, currentQueryString);
			//queryExpansion.extractSimilarTermsQuery(deepLearning, annotations,entitiesCandidates);
			//nextQuery = queryExpansion.getNextQuery();
			//currentQueryString = addTermsCurrentQuery(currentQueryString,nextQuery);
			//evaluateDocuments();
			iter ++;
			
		}
		
		fitFinalDoc();
		//finalDocSet = urlScoreObject.urlScoreFunction(heidelTime,deepLearning,topicID, eventDate,finalDocSet,Integer.toString(iter),urls,initialQuery);
		sortFinalDoc();
	//	evaluateDocuments();
	//	sortFinalDoc();
		deepLearning.closeFiles();
		int currentDoc = 0;
		
		sb.append("<table style=\"width:100%\">");
		sb.append("<tr>");
		sb.append("<th>Rank</th>");
		sb.append("<th>Timestamp</th>");
		sb.append("<th>score</th>");
		sb.append("<th>article</th>");
		sb.append("<th>relevance</th>");
		sb.append("<th>URL</th>");
		sb.append("</tr>");
		
		PreProcess preprocess = new PreProcess ();
		PairDocumentSimilarity parser = new PairDocumentSimilarity ();
		HashSet <String> cs = new HashSet<String>();
		cs = queryExpansion.getCollectionSpecification();
		
		
		int articleNumber = 1;
		
		double higherPrecision = 0.0f;
		StringBuilder sbFinalRes = new StringBuilder ();
		for (Entry<StringBuilder,Double> s : sbResults.entrySet())
		{
			if (s.getValue() > higherPrecision)
			{
				higherPrecision = s.getValue();
				sb = s.getKey();
				
			}
		}
		
		higherPrecision = 0.0f;
		
		for (Entry<StringBuilder,Double> s : sbRes.entrySet())
		{
			if (s.getValue() > higherPrecision)
			{
				higherPrecision = s.getValue();
				sbFinalRes = s.getKey();
				
			}
		}
		precisionAt20 = evaluator.getPrecisionAtn(sbFinalRes, 20);
		nDCG = evaluator.getnDCGAtn(sbFinalRes, 20);
		
	/*	for(Entry<LivingKnowledgeSnapshot, Double> s : finalDocSet.entrySet())
		{
			
			String relevance = evaluator.getArticleRelevance(s.getKey().getDocId());
			
		//	sbRes.append(s.getKey().getDocId() + "\n");
			if (articleNumber > maxDoc)
				break;
			String snippet;
			if (s.getKey().getText().length() <= 100)
				snippet = s.getKey().getText();
			else
				snippet = s.getKey().getText().substring(0, 100);
			BufferedWriter page = new BufferedWriter
	    		    (new OutputStreamWriter(new FileOutputStream(articleNumber+".txt"),"UTF-8"));
			sb.append("<tr>");
			sb.append("<td>" + articleNumber + "</td>");
			sb.append("<td>" + s.getKey().getDate() + "</td>");
			sb.append("<td>" + s.getKey().getScore() + "</td>");
			sb.append("<td>" + snippet + "</td>");
			sb.append("<td>" + relevance + "</td>");
			sb.append("<td><a href=\"" + articleNumber + ".txt"+"\">" + s.getKey().getUrl() + "</a>" + "</td>");
			articleNumber++;
			page.write(s.getKey().getText());
			page.close();
		}
		sb.append("</table>");
		sb.append("</body></html>");*/
		out.write(sb.toString());
		res.write(sbFinalRes.toString());
		res.close();
		out.close();
		
		for(Entry<String, Integer> s : queryTerms.entrySet())
		{
			System.out.println (s.getKey() + " " + s.getValue());
			
		}
		
	}

public double getPrecisionAt20() {
		return precisionAt20;
	}

	public void setPrecisionAt20(double precisionAt20) {
		this.precisionAt20 = precisionAt20;
	}

public LivingKnowledgeEvaluation getEvaluator() {
		return evaluator;
	}

	public void setEvaluator(LivingKnowledgeEvaluation evaluator) {
		this.evaluator = evaluator;
	}

public double getBestMAP() {
		return bestMAP;
	}

	public void setBestMAP(double bestMAP) {
		this.bestMAP = bestMAP;
	}

public int getLimit() {
		return limit;
	}

	public void setLimit(int limit) {
		this.limit = limit;
		elasticUtil.setLimit(limit);
	}

	/*public void readDomains () throws IOException
	{
		File f;
		if (localmode)			
			 f = new File ("/Users/tarcisio/complete.txt");
		else
			 f = new File ("/home/souza/complete.txt");
		FileReader fr = new FileReader (f);
		BufferedReader br = new BufferedReader (fr);
		
		String line;
		
		while ((line=br.readLine())!=null)
		{
			domains.add(line);
		}
		
		
	}
	*/
	public void addQueryTerms (String q)
	{
		StringTokenizer token = new StringTokenizer (q);
		
		while (token.hasMoreTokens())
		{
			String current = token.nextToken();
			if (queryTerms.containsKey(current))
			{
				int currentFreq = queryTerms.get(current);
				queryTerms.put(current, currentFreq+1);
			}
			else
				queryTerms.put(current, 1);
		}	
	}
	
	private void handleDuplicates(HashMap<LivingKnowledgeSnapshot, Double> articles2,String iter) throws MalformedURLException {
		
		HashMap<LivingKnowledgeSnapshot, Double> artWithDup = new HashMap<LivingKnowledgeSnapshot, Double>();
		articlesWithoutDuplicates.clear();
		articlesWithoutDuplicates = new  HashMap<String,Article>();
		
		for(Entry<LivingKnowledgeSnapshot, Double> s : articles2.entrySet()) {		
			
			if (urls.containsKey(s.getKey().getUrl()))
				continue;
			else
			{
				artWithDup.put(s.getKey(),s.getValue());
				urls.put(s.getKey().getUrl(),iter);
			}
		}
		
		urls.clear();
		articles = new HashMap<LivingKnowledgeSnapshot,Double>(artWithDup);
	
	}
	
	@SuppressWarnings("unchecked")
	public void processQuery (String query,String field,String iter) throws Exception
	{
			 elasticUtil.setKeywords(query);
			 elasticUtil.setField(field);
			 elasticUtil.setLimit(limit);
			 elasticUtil.run();
			 HashMap<LivingKnowledgeSnapshot, Double> currentDocs = new HashMap<LivingKnowledgeSnapshot, Double>();
			 articles = (HashMap<LivingKnowledgeSnapshot, Double>) elasticUtil.getResults();
		/*	 
			 for(Entry<LivingKnowledgeSnapshot, Double> s : currentDocs.entrySet())
				{
					//if (!urls.contains(s.getKey().getUrl()))
						
					if (!urls.containsKey(s.getKey().getUrl()))
					{
						articles.put(s.getKey(), s.getValue());
						urls.put(s.getKey().getUrl(), iter);
					}
				}
				
				*/
	}	

	public String getField() {
		return field;
	}

	public void setField(String field) {
		this.field = field;
		elasticUtil.setField(field);
	}

	public void fitFinalDoc ()
	{
		for(Entry<LivingKnowledgeSnapshot, Double> s : retrievedDocuments.entrySet())
		{
			
			finalDocSet.put(s.getKey(), s.getKey().getScore());
		}
	}
	
	public void sortFinalDoc ()
	{
		
		Map<LivingKnowledgeSnapshot, Double> ordered = sortByComparator (finalDocSet,false);
		finalDocSet.clear();
		finalDocSet = (HashMap<LivingKnowledgeSnapshot, Double>) ordered;
	
	}
	public void populateRetrivedDocuments () throws IOException, DocumentCreationTimeMissingException
	{
		
		for(Entry<LivingKnowledgeSnapshot, Double> s : articles.entrySet())
		{
			//if (!urls.contains(s.getKey().getUrl()))
				retrievedDocuments.put(s.getKey(), s.getValue());
		}
		
	}
	
	public void closeConnection ()
	{
		elasticUtil.closeConnection();
	}
	
	private static Map<LivingKnowledgeSnapshot, Double> sortByComparator(Map<LivingKnowledgeSnapshot, Double> unsortMap, final boolean order)
	{

	            List<Entry<LivingKnowledgeSnapshot, Double>> list = new LinkedList<Entry<LivingKnowledgeSnapshot, Double>>(unsortMap.entrySet());

	            // Sorting the list based on values
	            Collections.sort(list, new Comparator<Entry<LivingKnowledgeSnapshot, Double>>()
	            {
	                public int compare(Entry<LivingKnowledgeSnapshot, Double> o1,
	                        Entry<LivingKnowledgeSnapshot, Double> o2)
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
	            Map<LivingKnowledgeSnapshot, Double> sortedMap = new LinkedHashMap<LivingKnowledgeSnapshot, Double>();
	            for (Entry<LivingKnowledgeSnapshot, Double> entry : list)
	            {
	                sortedMap.put(entry.getKey(), entry.getValue());
	            }

	            return sortedMap;
	}
	
	public String removeDuplicateQuery (String currentQ)
	{
		String queryOutput ="";
		HashSet<String> queryTerms = new HashSet<String> ();
		
		StringTokenizer cQuery = new StringTokenizer (currentQ);
		
		while (cQuery.hasMoreTokens())
		{
			String cTerm = cQuery.nextToken();
			if (!queryTerms.contains(cTerm))
			{
				queryOutput += " " + cTerm;
				queryTerms.add(cTerm);
			}
		}
		
		return queryOutput;
				
		
		
	}
	
	public String addTermsBestQuery (String currentQuery)
	{
		StringTokenizer token = new StringTokenizer (bestQuery);
		String outputQuery = currentQuery;
		while (token.hasMoreTokens())
		{
			String term = token.nextToken();
			if (outputQuery.contains(term))
				continue;
			outputQuery = outputQuery + " " + term;
		}
		
		return outputQuery;
		
	}
	public String addTermsCurrentQuery (String currentQuery,HashSet<String> nextQ)
	{
		
		
		Iterator<String> iterator = nextQ.iterator();
		int size = nextQ.size();
		int position = 0;
		while (iterator.hasNext()) 
		{
		    if (position>terms)
		    	break;
			if (position==size)
			{
				currentQuery = currentQuery + iterator.next().toString();
			}
			else
				currentQuery = currentQuery + iterator.next().toString() + " ";
			
			position++;
			
		}
		
		return currentQuery;
		
	}
	
}
