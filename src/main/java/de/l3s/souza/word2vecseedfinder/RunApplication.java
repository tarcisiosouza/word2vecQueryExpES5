package de.l3s.souza.word2vecseedfinder;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Properties;
import java.util.Random;
import java.util.logging.LogManager;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


import de.l3s.souza.learningtorank.Term;
import de.l3s.souza.learningtorank.TermUtils;
import de.l3s.souza.evaluation.Point;

public class RunApplication {

	private static String propFileName = "seedfinderparam.properties";
	private static String collection;
	private static double currentMap;
	private static double globalCurrentMap;
	private static  Properties config;
	private static int limit;
	private static int maxSimTerms;
	private static int maxDoc;
	private static int maxIter;
	private static String field;
	private static int terms;
	private static String initialQuery;
	private static double alpha;
	private static double beta;
	private static double gama;
	private static double scoreParam;
	private static double totalPrecisionat20;
	private static double totalnDCGat20;
	private static double globalTotalPrecisionat20;
	private static double globalTotalnDCGat20;
	private static String runname;
	private static int maxUsedFreqTerm;
	private static String features;
	private static double lambda;
	private static int windowsize;
	private static deepLearningUtils deepLearning;
	private static int candidateTerms;
	private static boolean L2r;
	private static boolean bm25;
	private static boolean debug;
	private static boolean tempSeg;
	private static boolean subsetgeneration;
	private static boolean tempkg;
	static Logger logger = LoggerFactory.getLogger(RunApplication.class);
	
	private static ArrayList<Point> overallPrecRecall = new ArrayList<Point> ();
	private static ArrayList<Point> overallPrecRecallGlobal = new ArrayList<Point> ();
	
	public static void main (String args[]) throws Exception
	{
		
		
		//LogManager.getLogManager().reset();
		
		ArrayList<String> random = new ArrayList<String>();
		BufferedWriter global = new BufferedWriter
    		    (new OutputStreamWriter(new FileOutputStream("PrecRecallCurveGlobal.txt"),"UTF-8"));
		
		BufferedWriter outPart = new BufferedWriter
    		    (new OutputStreamWriter(new FileOutputStream("PartialPrecRecall.txt"),"UTF-8"));
		
		BufferedWriter topics = new BufferedWriter
    		    (new OutputStreamWriter(new FileOutputStream("RandomTopics.txt"),"UTF-8"));
		
		InputStream inputStream = RunApplication.class.getClassLoader().getResourceAsStream(propFileName);
		config = new Properties ();
		double totalMap = 0.0f;
		double totalMapGlobal = 0.0f;
		int total = 0;
		int totalGlobal = 0;
		
		if (inputStream != null) {
			config.load(inputStream);
		} else {
			global.close();
			topics.close();
			throw new FileNotFoundException("property file '" + propFileName + "' not found in the classpath");
			
		}
		
		totalPrecisionat20 = 0;
		globalTotalPrecisionat20 = 0;
		globalTotalnDCGat20 = 0;
		totalnDCGat20 = 0;
		L2r = Boolean.parseBoolean(config.getProperty("L2r"));
		tempkg = Boolean.parseBoolean(config.getProperty("tempkg"));
		bm25 = Boolean.parseBoolean(config.getProperty("bm25"));
		debug = Boolean.parseBoolean(config.getProperty("debug"));
		candidateTerms = Integer.parseInt(config.getProperty("candidateTerms"));
		features = config.getProperty("features");
		collection = config.getProperty("collection");
		lambda = Double.parseDouble(config.getProperty("lambda"));
		windowsize=Integer.parseInt(config.getProperty("windowsize"));
		limit = Integer.parseInt(config.getProperty("limit"));
		maxUsedFreqTerm = Integer.parseInt(config.getProperty("maxUsedFreqTerm"));
		maxSimTerms = Integer.parseInt(config.getProperty("maxSimTerms"));
		maxDoc = Integer.parseInt(config.getProperty("maxDoc"));
		field =config.getProperty("field");
		terms = Integer.parseInt(config.getProperty("terms"));
		maxIter = Integer.parseInt(config.getProperty("maxIter"));
		alpha = Double.parseDouble(config.getProperty("alpha"));
		beta = Double.parseDouble(config.getProperty("beta"));
		gama = Double.parseDouble(config.getProperty("gama"));
		scoreParam = Double.parseDouble(config.getProperty("scoreParam"));
		runname = config.getProperty("runname");
		tempSeg = Boolean.parseBoolean(config.getProperty("tempsegment"));
		subsetgeneration = Boolean.parseBoolean(config.getProperty("subsetgeneration"));
		Term term = new Term ("");
		TermUtils termUtils;
		File file;
		
		if (collection.contentEquals("ntcir_12"))
		{
			termUtils = new TermUtils ("","/home/souza/NTCIR-eval/ntcir12_Temporalia_taskdata/Evaluation Data/",term,windowsize,lambda,features,"ntcir_12");
			file = new File ("/home/souza/NTCIR-eval/ntcir12_Temporalia_taskdata/Test Collection/NTCIR12_Temporalia2_FormalRun_TDR_En.txt");
		}
		else
		{
			termUtils = new TermUtils ("","/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/",term,windowsize,lambda,features,"ntcir_11");
			file = new File ("/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/NTCIR-11TIRTopicsFormalRun.txt");
		}
		//File file = new File ("/home/souza/NTCIR-eval/ntcir12_Temporalia_taskdata/TaskData/TIR/NTCIR-11TIRTopicsFormalRun.txt");

		FileReader fr = new FileReader (file);
		BufferedReader br = new BufferedReader (fr);
		String id;
		String description = null;
		String query_time = null;
		String title = null;
		String line;
		String topic = null;
		String atempQuery="";
		
		Query query = new Query (maxUsedFreqTerm,runname,limit,field,terms,maxSimTerms,candidateTerms,maxDoc,
				maxIter,alpha,beta,gama,scoreParam,L2r,collection,debug,tempSeg,tempkg);
		
		ArrayList<String> tempTopics = new ArrayList<String>();
		
		tempTopics.add("a");
		tempTopics.add("f");
		tempTopics.add("r");
		tempTopics.add("p");
		int indexTempTopics = 0;
		while ((line=br.readLine())!=null)
		{
			
			if (line.contains("<id>"))
			{
				final Pattern pattern = Pattern.compile("<id>(.+?)</id>");
				final Matcher m = pattern.matcher(line);
				m.find();
				id = m.group(1);
			}
			
			if (line.contains("<title>"))
			{
				final Pattern pattern = Pattern.compile("<title>(.+?)</title>");
				final Matcher m = pattern.matcher(line);
				m.find();
				title = m.group(1);
			}
			if (line.contains("<description>"))
			{
				Pattern pattern = Pattern.compile("<description>(.+?)</description>");
				Matcher m = pattern.matcher(line);
				m.find();
				description = m.group(1);
			}
			
			if (line.contains("<query"))
			{
				Pattern pattern = Pattern.compile("<query_issue_time>(.+?)</query_issue_time>");
				Matcher m = pattern.matcher(line);
				m.find();
				query_time = m.group(1);
			}
			
			if (line.contains("<subtopic id"))
			{
				
				Pattern pattern = Pattern.compile("<subtopic id=\"(.+?)\"");
				Matcher m = pattern.matcher(line);
				m.find();
				topic = m.group(1);
				line = line.replaceAll("<[^>]+>", "");
								
				int i= 0;
				for (i=0;;i++)
				{
					
					if (Character.isAlphabetic(line.charAt(i)))
						break;
				}
				
				line = line.substring(i, line.length());
				initialQuery = line;
				int number = Integer.parseInt(topic.substring(0,3));
				if (topic.contains(tempTopics.get(indexTempTopics)))
				{
					atempQuery = initialQuery;
					total++;
					totalGlobal++;
				//	random.add(topic);
					
				}
				else
					continue;
				System.out.println("Current topic: "+topic);
				
				
				if (!topic.contentEquals("037a") )
					continue;
				/*if (number < 33)
					continue;*/
			/*	if (topic.contentEquals("001p"))
				{*/
				//public TermUtils (String topic, String path, Term term, int windowSize,double lambda, String features)
				termUtils.setTopic(topic);
				query.setBestMAP(0.0);
				query.run(termUtils, topic, title, title+" "+description+" "+line, title, query_time,bm25,subsetgeneration);
				totalMap = totalMap + query.getBestMAP();
				totalMapGlobal = totalMapGlobal + query.getBestMAP();
				
				currentMap = totalMap / total;
				globalCurrentMap = totalMapGlobal / totalGlobal;
				totalPrecisionat20 = totalPrecisionat20 + query.getPrecisionAt20();
				globalTotalPrecisionat20 = globalTotalPrecisionat20 + query.getPrecisionAt20();
				totalnDCGat20 = totalnDCGat20 + query.getnDCG();
				globalTotalnDCGat20 = globalTotalnDCGat20 + query.getnDCG();
				
				System.out.println("Current MAP:" + currentMap);
				System.out.println("Current P@20:" + totalPrecisionat20/total);
				System.out.println("Current nDCG@20:" + totalnDCGat20/total);
				System.out.println("Current Global MAP:" + globalCurrentMap);
				System.out.println("Current Global P@20:" + globalTotalPrecisionat20/totalGlobal);
				System.out.println("Current Global nDCG@20:" + globalTotalnDCGat20/totalGlobal);

				ArrayList<Point> currentPrecRecall = query.getEvaluator().getBestprecRecall();
				
				if (overallPrecRecall.isEmpty())
					overallPrecRecall = currentPrecRecall; 
				else
					{	
						int size=0;
						StringBuilder sbPartial = new StringBuilder ();
						sbPartial.append(topic + "\n");
						if (overallPrecRecall.size() < currentPrecRecall.size())
							size = overallPrecRecall.size();
						else
							size = currentPrecRecall.size();

						for (int cPoint=0;cPoint<size;cPoint++)
						{
							Point p = new Point ();
							Point q = new Point ();
							p = currentPrecRecall.get(cPoint);
							q = overallPrecRecall.get(cPoint);
							
							q.setPrecision( (q.getPrecision()+p.getPrecision()) );
							q.setRecall( (q.getRecall()+p.getRecall()) );
							sbPartial.append(q.getRecall() + " " + q.getPrecision() + "\n");
							
							overallPrecRecall.set(cPoint, q);
						}
						
						outPart.write(sbPartial.toString());
					
					}
				
		/*		if (overallPrecRecallGlobal.isEmpty())
					overallPrecRecallGlobal = currentPrecRecall; 
				else
					{	
						int size=0;
				
						if (overallPrecRecallGlobal.size() < currentPrecRecall.size())
							size = overallPrecRecallGlobal.size();
						else
							size = currentPrecRecall.size();

						for (int cPoint=0;cPoint<size;cPoint++)
						{
							Point p = new Point ();
							Point q = new Point ();
							p = currentPrecRecall.get(cPoint);
							q = overallPrecRecallGlobal.get(cPoint);
							
							q.setPrecision( (q.getPrecision()+p.getPrecision()) );
							q.setRecall( (q.getRecall()+p.getRecall()) );
							//sbPartial.append(q.getRecall() + " " + q.getPrecision() + "\n");
							overallPrecRecallGlobal.set(cPoint, q);
						}
						
						
						//outPart.write(sbPartial.toString());
					
					}
				
			/*	break;	
				}*/
					
			}
			
			if (topic!=null && topic.contains("50"))
			{
				
				StringBuilder sb = new StringBuilder ();
				for (int j=0;j<overallPrecRecall.size();j++)
				{
					Point q = new Point ();
					
					q = overallPrecRecall.get(j);
					double OverAllRecall = (double) q.getRecall()/total;
					double OverAllPrecision = (double) q.getPrecision()/total;
					
					sb.append( OverAllRecall + " " + OverAllPrecision + "\n");
				}
				
				BufferedWriter currentOut = new BufferedWriter
		    		    (new OutputStreamWriter(new FileOutputStream("PrecRecallCurve_" + tempTopics.get(indexTempTopics) +".txt"),"UTF-8"));
				
				totalPrecisionat20 = totalPrecisionat20/total;
				totalnDCGat20 = totalnDCGat20/total;
				currentOut.write("MAP " + currentMap + "\n");
				currentOut.write("P@20 " + totalPrecisionat20 + "\n");
				currentOut.write("nDCG@20 " + totalnDCGat20 + "\n");

				currentOut.write(sb.toString());
				currentOut.close();
				totalPrecisionat20 = 0;
				total = 0;
				totalMap = 0.0f;
				totalnDCGat20 = 0;
				overallPrecRecall.clear();
				indexTempTopics ++;
				topic = null;
				if (indexTempTopics<=3)
				{
					fr = new FileReader (file);
					br = new BufferedReader (fr);
				}
				else
					break;
			}
			
		}
		
		
		
		StringBuilder sb = new StringBuilder ();
	/*	for (int j=0;j<overallPrecRecallGlobal.size();j++)
		{
			Point q = new Point ();
			
			q = overallPrecRecallGlobal.get(j);
			double OverAllRecall = (double) q.getRecall()/totalGlobal;
			double OverAllPrecision = (double) q.getPrecision()/totalGlobal;
			
			sb.append( OverAllRecall + " " + OverAllPrecision + "\n");
		} */
		//

		
		globalTotalPrecisionat20 = globalTotalPrecisionat20/totalGlobal;
		globalTotalnDCGat20 = globalTotalnDCGat20/totalGlobal;
		global.write("MAP " + globalCurrentMap + "\n");
		global.write("P@20 " + globalTotalPrecisionat20 + "\n");
		global.write("nDCG@20 " + globalTotalnDCGat20 + "\n");

		//global.write(sb.toString());
		global.close();
	/*	
		StringBuilder randomTopics = new StringBuilder ();
		
		int randSize = random.size();
		
		HashSet<Integer> generated = new HashSet<Integer>();
		Random randomGenerator = new Random ();
		for (int value=0;value<10;value++)
		{
			int randomInt = randomGenerator.nextInt(random.size());
			while (generated.contains(randomInt))
				randomInt = randomGenerator.nextInt(random.size());
			
			generated.add(randomInt);
			
			String topicGenerated = random.get(randomInt);
			randomTopics.append(topicGenerated + "\n");
		}
		
		topics.write(randomTopics.toString());
		topics.close();
	*/
	}
	
}

	
