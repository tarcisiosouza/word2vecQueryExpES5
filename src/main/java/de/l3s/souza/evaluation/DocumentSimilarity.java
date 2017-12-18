package de.l3s.souza.evaluation;

/* 

For json support please download last version of json.simple from    http://json-simple.googlecode.com/
  tested with version http://json-simple.googlecode.com/files/json-simple-1.1.1.jar
  
For compiling and running example, please use following example  
javac  -cp json-simple-1.1.1.jar: DocumentSimilarity.java ; java  -cp json-simple-1.1.1.jar:   DocumentSimilarity

Author: Vitalie Scurtu
www.scurtu.it
*/


import java.net.*;
import java.util.HashSet;
import java.io.*;

import org.json.simple.JSONObject;
import org.json.simple.JSONValue;



public class DocumentSimilarity
{
/*

 public double getScoreSimilarity(String text1, String text2) throws Exception {
    
    String urlToCall = "http://www.scurtu.it/apis/documentSimilarity";
    String content = "doc1=" + URLEncoder.encode(text1) +
		      "&doc2=" + URLEncoder.encode(text2);
    
    URL url = new URL(urlToCall); 
    HttpURLConnection connection = (HttpURLConnection) url.openConnection();                       
    connection.setDoOutput(true); 
    connection.setDoInput (true);
    connection.setUseCaches (false);        
    connection.setInstanceFollowRedirects(false); 
    connection.setRequestMethod("POST"); 
    connection.setRequestProperty("Content-Type", "text/plain"); 
    connection.setRequestProperty("charset", "utf-8");
    connection.connect();
    
    
    DataOutputStream output = new DataOutputStream(connection.getOutputStream());
    output.writeBytes(content);
    output.flush();
    output.close();
    
    StringBuilder strBuffer = new StringBuilder();
    String str = null;
    DataInputStream input = new DataInputStream (connection.getInputStream());
            while (null != ((str = input.readLine()))) {
                strBuffer.append(str);
      }
      
    Object obj=JSONValue.parse(strBuffer.toString());
    JSONObject jsonObj = (JSONObject)obj;    
   // System.out.println(jsonObj.get("result"));

    return (Double.parseDouble(jsonObj.get("result").toString()));
    
    }
 
 public double getHigherScoreSimilarity (String text1, HashSet<String> collection) throws Exception
 {
	 double currentHigher = 0.0f;
	 
	for (String s : collection) {
		double current = getScoreSimilarity (text1,s);
		if (current > currentHigher)
			currentHigher = current;
	}
	 
	 return currentHigher;
	 
 }
 
 */
}