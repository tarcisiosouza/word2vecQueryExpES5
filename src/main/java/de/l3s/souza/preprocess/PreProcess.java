package de.l3s.souza.preprocess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.StringTokenizer;

public class PreProcess {
	
	 private static HashSet<String> stopwords = new HashSet<String>(); 
	 private static ArrayList<String> vowels = new ArrayList<String>();
	 
	 public PreProcess () {
		   vowels.add("a");
	       vowels.add("e");
	       vowels.add("i");
	       vowels.add("o");
	       vowels.add("u");
		 
		 try 
  	   	  {
  	   	   File fl = new File("/home/souza/stopwords_en.txt");
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
	 
	 public String removeDuplicates (String incoming)
	 {
		 String outcome="";
		 
		 StringTokenizer token = new StringTokenizer (incoming);
		 
		 while (token.hasMoreTokens())
		 {
			 String term = token.nextToken().toLowerCase();
			 if (!outcome.contains(term))
			 {
				 if (outcome.contentEquals(""))
				 	outcome = outcome + term;
				 else
					 outcome = outcome + " " + term;
			 }
		 }
		 
		 return outcome;
	 }
	 
	 
	 public String removeStopWords (String str)
		{
			String newStr="";
			//String input = str.replaceAll("[-+.^:,]","");
			
			StringTokenizer token = new StringTokenizer (str);
			while (token.hasMoreTokens())
			{
				String term = token.nextToken().toLowerCase();
				term = removePunctuation(term);
				if (!stopwords.contains(term) && term.length()>1)
				{
					if (newStr.contentEquals(""))
						newStr = newStr + term;
					else
						newStr = newStr + " " +term;
				}
			}
			return newStr;
		}
	 
	 public boolean isStopWord (String str)
	 {
		 
		 if (stopwords.contains(str))
		 	return true;
		 
		 return false;
	 }
	 
	
	//Clean the URL, removing stopwords and other unused fields
		public String preProcessUrl (String u) throws MalformedURLException
		{
			String path;
			String final_url = null;
			URL url = new URL (u);
			path = url.getPath();
			path =path.replaceAll("[^\\w\\s]", " ").replaceAll("_", " ");
			StringTokenizer token = new StringTokenizer (path);
			
			while (token.hasMoreElements())
	     	{
				String str = token.nextToken();
			
				if (isValidToken(str))
				{		
					if (final_url != null)
						final_url = final_url + " " +str;
					else
						final_url = str;
				}
	     	}
			
			if (final_url == null)
				return "";
			else
				return final_url;
		}
		
		public static boolean isValidToken (String str)
		{
			int position = 0;
			String currentChar;
			
			if (stopwords.contains(str.toLowerCase()) || str.length()<=2)
				return false;
			
			try {
				
				int number = Integer.parseInt(str);
				if (str.length()>4)
				{
					int year = Integer.parseInt(str.substring(0, 4));
					if (year < 1970)
						return false;
				}
				else
					if (number < 1970)
						return false;
			} catch (Exception e)
			{
				
				
			}
				return true;
		}
		
		
		public static boolean isNumberConcatChar (String str)
		{
			int size = str.length();
			
			for (int i=0;i<str.length();i++)
			{
				if (Character.isDigit(str.charAt(i)))
				{
					return true;
				}
				
			}
			
			return false;
			
		}
		
		public String removePunctuation (String str)
		{
			String newStr = "";
			for (int i=0;i<str.length();i++)
			{
				if (Character.isSpaceChar(str.charAt(i)) || Character.isAlphabetic(str.charAt(i)) || Character.isDigit(str.charAt(i)))
					newStr = newStr + str.charAt(i);
			}
			
			return newStr;
			
		}
		
		public String removeNonLettersString (String incomingStr)
		{
			String newStr = "";
			char[] incomingStrChar = incomingStr.toCharArray();
			for (int i=0;i<incomingStrChar.length;i++)
			{
				Character character = incomingStrChar[i];
				if (Character.isAlphabetic(character))
					newStr = newStr + character;
			}
			return newStr;
		}
		
		public String removeNonLettersFromText (String text)
		{
			String newText = "";
			char[] strChar;
			
			if (text==null)
				return "";
			strChar = text.toCharArray();
				
			for (int i=0;i<strChar.length;i++)
			{
				if (Character.isLetterOrDigit(strChar[i]) || Character.isWhitespace(strChar[i]) || strChar[i]=='’')
					newText = newText + strChar[i];
				
				if (!(Character.isLetterOrDigit(strChar[i])) && !(Character.isWhitespace(strChar[i])) && ((i+1)<strChar.length) 
						&& strChar[i]!='’')
				{
					if (Character.isLetterOrDigit(strChar[i+1]))
						newText = newText + " ";
				}
			}
			
			return newText;
			
		}
		
		public static boolean isNumber (String str)
		{
		
		    try{  
	            Integer.parseInt(str);  
	            return true;  
	        }catch(Exception e){
	        try {	
	        	Float.parseFloat(str);
	        	return true;
	        }catch (Exception f) {
	        	return false;
	        }  
	        }  
		
		}
		

}
