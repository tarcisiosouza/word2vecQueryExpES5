package de.l3s.souza.learningtorank;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.l3s.souza.word2vecseedfinder.Query;

public class DataGenerationL2R {

		private static String propFileName = "l2r.properties";
		private static  Properties config;
		private static String collection;
		private static int relevance;
		private static int candidateTerms;
		private static String query_id;
		private static String id;
		private static String title;
		private static String description;
		private static String query_id_desc;
		private static String query_id_title;
		private static String topic;
		private static String initialQuery;
		private static String atempQuery;
		private static String features;
		private static double lambda;
		private static int windowsize;
		private static int windowsizePRF;
		private static int totalFeedbackDocuments;
		
		public static void main (String args[]) throws Exception
		{
			
			
			InputStream inputStream = DataGenerationL2R.class.getClassLoader().getResourceAsStream(propFileName);
			config = new Properties ();
			
			if (inputStream != null) {
				config.load(inputStream);
			} else {
				throw new FileNotFoundException("property file '" + propFileName + "' not found in the classpath");
			}
			
			features = config.getProperty("features");
			collection = config.getProperty("colleciton");
			lambda = Double.parseDouble(config.getProperty("lambda"));
			windowsize=Integer.parseInt(config.getProperty("windowsize"));
			windowsizePRF=Integer.parseInt(config.getProperty("windowsizePRF"));
			totalFeedbackDocuments=Integer.parseInt(config.getProperty("feedbackDocuments"));
			candidateTerms = Integer.parseInt(config.getProperty("candidateTerms"));
			BufferedWriter res = new BufferedWriter(new FileWriter("/home/souza/trainL2R_500.txt", true));
			StringBuilder sb = new StringBuilder ();
			File file = new File ("/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/NTCIR-11TIRTopicsFormalRun.txt");
			FileReader fr = new FileReader (file);
			BufferedReader br = new BufferedReader (fr);
			String line;
			int subtopicNumber = 0;
			
			Query query = new Query (totalFeedbackDocuments,"text",collection);
			Term term = new Term("");
			TermUtils termUtils = new TermUtils ("","/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/",term,windowsize,lambda,features,collection);
			while ((line=br.readLine())!=null)
			{
				
				if (line.contains("<id>"))
				{
					final Pattern pattern = Pattern.compile("<id>(.+?)</id>");
					final Matcher m = pattern.matcher(line);
					m.find();
					query_id_title = m.group(1)+"t";
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
					query_id_desc = id + "d";
				}
				
			/*	if (line.contains("<query"))
				{
					Pattern pattern = Pattern.compile("<query_issue_time>(.+?)</query_issue_time>");
					Matcher m = pattern.matcher(line);
					m.find();
					query_time = m.group(1);
				}
				*/
				if (line.contains("<subtopic id"))
				{
					subtopicNumber++;
					
					Pattern pattern = Pattern.compile("<subtopic id=\"(.+?)\"");
					Matcher m = pattern.matcher(line);
					m.find();
					query_id = topic = m.group(1);
					line = line.replaceAll("<[^>]+>", "");
									
					int i= 0;
					for (i=0;;i++)
					{
						
						if (Character.isAlphabetic(line.charAt(i)))
							break;
					}
					
					line = line.substring(i, line.length());
					initialQuery = line;
					
					if (topic.contains("a"))
					{
						atempQuery = initialQuery;
						
					}
					System.out.println("Current topic: "+topic);
					int number = Integer.parseInt(topic.substring(0,3));
						
					/*if ((!topic.contentEquals("001a")) && (!topic.contentEquals("001p")))
							break;*/
						//System.out.println(query.getCurrentQuery());
						query.setTopic(topic);
						query.setCurrentQuery(initialQuery);
						query.setLimit(totalFeedbackDocuments);
						query.setField("text");
						query.processCurrentQuery();
						initialQuery = query.getCurrentQuery();
						
						double initialAvPrec = query.getAvPrecision();
						HashMap<String,Double> terms = query.getCandidateTerms();
						
						int termsTotal = 0;
						for (Entry<String, Double> s:terms.entrySet() )
						{
							termsTotal++;
							query.setCurrentQuery(initialQuery+" "+s.getKey());
							query.setLimit(totalFeedbackDocuments);
							query.setField("text");
							query.processCurrentQuery();
							//Query expQuery = new Query(initialQuery+" "+s.getKey(),topic,totalFeedbackDocuments,"text");
						//	System.out.println(expQuery.getCurrentQuery());
							double currentAvPrec = query.getAvPrecision();
							
							if ((currentAvPrec - initialAvPrec) >= 0)
								relevance = 1;
							else
								relevance = 0;
							
							term = new Term(s.getKey());
							termUtils.setTopic(topic);
							termUtils.setTerm(term);
							//TermUtils termUtils = new TermUtils (topic,"/home/souza/NTCIR-eval/ntcir11_Temporalia_taskdata/TaskData/TIR/",term,windowsize,lambda,features);
							term = termUtils.calculateL2Rfeatures(initialQuery,query,totalFeedbackDocuments);
							HashMap<Integer,Double> features = new HashMap<Integer,Double>();
							
							features = term.getFeaturesVector();
							sb.append(relevance+" "+"qid:"+query_id+" ");
							int indice = 0;
							
							for (Entry<Integer,Double> feature : features.entrySet())
							{
								if (indice<=features.size())
									sb.append(feature.getKey()+":"+feature.getValue() + " ");
								else
									sb.append(feature.getKey()+":"+feature.getValue());
								indice++;
							}
								
							sb.append(" #"+term.getTermString()+"\n");
							
							if (termsTotal > candidateTerms)
								break;
						}
			
				}
				
				
			}
			
			query.closeConnection();
			res.write(sb.toString());
			res.close();
			
		}
}
