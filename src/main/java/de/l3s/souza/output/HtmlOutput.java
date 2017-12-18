package de.l3s.souza.output;

import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.util.HashMap;
import java.util.Map.Entry;

import de.l3s.souza.esfive.LivingKnowledgeSnapshot;
import de.l3s.souza.evaluation.LivingKnowledgeEvaluation;

public class HtmlOutput {

	private StringBuilder sb;
	private StringBuilder sbRes;
	
	public StringBuilder getSb() {
		return sb;
	}

	public void setSb(StringBuilder sb) {
		this.sb = sb;
	}

	public void outputArticlesHtml (StringBuilder incomingSb,HashMap<LivingKnowledgeSnapshot, Double> articles, String iter, LivingKnowledgeEvaluation evaluator, String topicID, String runname) throws IOException
	{
		int rank = 1;
		//BufferedWriter res = new BufferedWriter(new FileWriter("/home/souza/NTCIR-eval/ntcir12_Temporalia_taskdata/Evaluation Data/"+topicID+"/"+topicID+"."+runname+iter+".res", true));
		sbRes = new StringBuilder ();
		sb = new StringBuilder ();
		sb.append(incomingSb);
		sb.append("<table style=\"width:100%\">");
		sb.append("<tr>");
		sb.append("<th>Rank</th>");
		sb.append("<th>doc-id</th>");
		sb.append("<th>Timestamp</th>");
		sb.append("<th>score</th>");
		sb.append("<th>article</th>");
		sb.append("<th>relevance</th>");
		sb.append("<th>URL</th>");
		sb.append("</tr>");
		
		BufferedWriter outtIter = new BufferedWriter
    		    (new OutputStreamWriter(new FileOutputStream(iter+"_iter.html"),"UTF-8"));
		for(Entry<LivingKnowledgeSnapshot, Double> s : articles.entrySet())
		{
			
			String relevance = evaluator.getArticleRelevance(s.getKey().getDocId());
			sbRes.append(s.getKey().getDocId() + "\n");

			String snippet;
			if (s.getKey().getText().length() <= 500)
				snippet = s.getKey().getText();
			else
				snippet = s.getKey().getText().substring(0, 500);
			
			sb.append("<tr>");
			sb.append("<td>" + rank + "</td>");
			sb.append("<td>" + s.getKey().getDocId() + "</td>");
			sb.append("<td>" + s.getKey().getDate() + "</td>");
			sb.append("<td>" + s.getKey().getScore() + "</td>");
			sb.append("<td>" + snippet + "</td>");
			sb.append("<td>" + relevance + "</td>");
			sb.append("<td><a href=\"" + s.getKey().getUrl() + ".txt"+"\">" + s.getKey().getUrl() + "</a>" + "</td>");
			rank++;
			
		}
		sb.append("</table>");
		sb.append("</body></html>");
	//	res.write(sbRes.toString());
		outtIter.write(sb.toString());
		outtIter.close();
		//res.close();
		
	}

	public StringBuilder getSbRes() {
		return sbRes;
	}

	public void setSbRes(StringBuilder sbRes) {
		this.sbRes = sbRes;
	}
}
