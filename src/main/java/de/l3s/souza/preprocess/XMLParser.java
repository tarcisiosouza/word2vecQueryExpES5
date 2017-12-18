package de.l3s.souza.preprocess;

import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.w3c.dom.Node;
import org.w3c.dom.Element;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;

public class XMLParser {
	
	private Document loadXMLFromString(String xml) throws Exception
	{
	    DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
	    DocumentBuilder builder = factory.newDocumentBuilder();
	    InputSource is = new InputSource(new StringReader(xml));
	    return builder.parse(is);
	}
	
	//Get time expressions from TIMEML HeidelTime format
	public ArrayList<String> getValueTimeML (String xml) throws Exception
	{
		Document doc = loadXMLFromString(xml);
		ArrayList<String> timeExp = new ArrayList<String>();
		 doc.getDocumentElement().normalize();

	        //    System.out.println("Root element :" + doc.getDocumentElement().getNodeName());

	     NodeList docs = doc.getElementsByTagName("TIMEX3");
	     
	     for (int i = 0; i < docs.getLength(); i++) {
         	
	    	 timeExp.add(docs.item(i).getNodeValue());
	    	 
         	//String node = docs.item(i).getAttributes().getNamedItem("value").getTextContent();
         	
	     }
		return timeExp; 
	}
	
	public ArrayList<String> getValueTimeMLRegex (String xml) throws Exception
	{
		
		ArrayList<String> timeExp = new ArrayList<String>();
		
		final Pattern pattern = Pattern.compile("value=\"(.+?)\"");
		
	    final Matcher matcher = pattern.matcher(xml);
	    
	    while (matcher.find())
	    {
	    	timeExp.add(matcher.group());
	    }	
	     
		return timeExp; 
	}
}
