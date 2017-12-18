package de.l3s.souza.learningtorank;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.StringTokenizer;

public class Term {

	private String termString;	
	private int tf;
	private int df;
	private double idf;
	private int coOcurrencyQuery;
	private int pairCoOccurQuery;
	private int pairCoOccurQueryPrf;
	private int coOcurrencyQueryPrf;
	private double logCoOcurrencyQuery;
	private double logPairCoCoccurQuery;
	private double logFeedbackTermFreq;
	private double tfIdf;
	private double logTfIdf;
	private double logDf;
	private double logTf;
	private double logIdf;
	private double logTfDf;
	private int termProximity;
	private int feedbackTermFreq = 0;
	private double min;
	private double max;
	private double termDependenceScore = 0;
	private HashMap<Integer,Double> featuresVector = new HashMap<Integer,Double>();
	private HashMap<Integer,Double> selectedFeatures = new HashMap<Integer,Double>();
	
	public void updateMinMax (double feature)
	{
		
		if (featuresVector.isEmpty())
			min = max = feature;
		else
		{
			if (feature <=min)
				min = feature;
		
			if (feature >= max)
				max = feature;
		}
		
		//featuresVector.add(feature);
	}
	
	//min max normalization
	public void normalizeFeatures (String features)
	{
		StringTokenizer tokenFeature = new StringTokenizer (features,",");
		
		while (tokenFeature.hasMoreTokens())
		{
			if (selectedFeatures.isEmpty())
			{
				int index = Integer.parseInt(tokenFeature.nextToken());
				min = max = featuresVector.get(index);
				selectedFeatures.put(index, featuresVector.get(index));
			}
			else
			{
				int index = Integer.parseInt(tokenFeature.nextToken());
				double feature = featuresVector.get(index);
				updateMinMax (feature);
				selectedFeatures.put(index, feature);
			}
			
		}
		
		//selectedFeatures = softMax (selectedFeatures);
		
		double newFeature;
		
		for (Entry<Integer,Double> s: selectedFeatures.entrySet())
		{
			double current = s.getValue();
			newFeature = (current - min)/(max - min);
			selectedFeatures.put(s.getKey(), newFeature);
		}
		
	}
	
	public HashMap<Integer, Double> getFeaturesVector() {
		return featuresVector;
	}
		//softmax normalization
		private HashMap<Integer,Double> softMax (HashMap<Integer,Double> origin)
		{
			HashMap<Integer,Double> result = new HashMap<Integer,Double>();
			double sumExp=0;
			for (Entry<Integer,Double>  s : origin.entrySet() )
				sumExp = sumExp + Math.exp(s.getValue());
			
			for (Entry<Integer,Double>  s : origin.entrySet() )
			{
				double normalizedScore = Math.exp(s.getValue())/sumExp;
				result.put(s.getKey(), normalizedScore);
			}
			
			return result;
		}
	public HashMap<Integer, Double> getSelectedFeatures() {
		return selectedFeatures;
	}

	public int getPairCoOccurQueryPrf() {
		return pairCoOccurQueryPrf;
	}

	public void setPairCoOccurQueryPrf(int pairCoOccurQueryPrf,int index) {
		
		//updateMinMax(pairCoOccurQueryPrf);
		this.pairCoOccurQueryPrf = pairCoOccurQueryPrf;
		featuresVector.put(index,(double) pairCoOccurQueryPrf);
	}

	public int getCoOcurrencyQueryPrf() {
		return coOcurrencyQueryPrf;
	}

	public void setCoOcurrencyQueryPrf(int coOcurrencyQueryPrf, int index) {
		//updateMinMax(coOcurrencyQueryPrf);
		this.coOcurrencyQueryPrf = coOcurrencyQueryPrf;
		featuresVector.put(index,(double) coOcurrencyQueryPrf);
	}

	public int getFeedbackTermFreq() {
		return feedbackTermFreq;
	}

	public void setFeedbackTermFreq(int feedbackTermFreq, int index) {
		//updateMinMax(feedbackTermFreq);
		this.feedbackTermFreq = feedbackTermFreq;
		featuresVector.put(index,(double) feedbackTermFreq);
	}

	public void setLogFeedbackTermFreq (int index)
	{
		if (feedbackTermFreq==0)
			logFeedbackTermFreq = 0;
		else
		logFeedbackTermFreq = Math.log(feedbackTermFreq);
		//updateMinMax(logFeedbackTermFreq);
		featuresVector.put(index,(double) logFeedbackTermFreq);
	}
	
	public double getLogFeedbackTermFreq ()
	{
		if (feedbackTermFreq==0)
			return 0;
		return logFeedbackTermFreq;
	}
	
	public int getTermProximity() {
		return termProximity;
	}

	public void setTermProximity(int termProximity,int index) {
		//updateMinMax(termProximity);
		this.termProximity = termProximity;
		featuresVector.put(index,(double) termProximity);
		
	}

	public void setLogCoOcurrencyQuery(double logCoOcurrencyQuery, int index) {
		//updateMinMax(logCoOcurrencyQuery);
		this.logCoOcurrencyQuery = logCoOcurrencyQuery;
		featuresVector.put(index,logCoOcurrencyQuery);
	}

	public double getLogPairCoCoccurQuery() {
		
		return logPairCoCoccurQuery;
	}

	public void setLogPairCoCoccurQuery(double logPairCoCoccurQuery, int index) {
		//updateMinMax(logPairCoCoccurQuery);
		this.logPairCoCoccurQuery = logPairCoCoccurQuery;
		featuresVector.put(index,logPairCoCoccurQuery);
	}

	public int getPairCoOccurQuery() {
		return pairCoOccurQuery;
	}

	public void setPairCoOccurQuery(int pairCoOccurQuery,int index) {
		//updateMinMax(pairCoOccurQuery);
		this.pairCoOccurQuery = pairCoOccurQuery;
		featuresVector.put(index,(double) pairCoOccurQuery);
	}

	public Term (String termString)
	{
		this.termString = termString;
	}

	public String getTermString() {
		return termString;
	}

	public void setTermString(String termString) {
		
		this.termString = termString;
	}

	public int getTf() {
		return tf;
	}

	public int getCoOcurrencyQuery() {
		return coOcurrencyQuery;
	}

	public void setLogCoOcurrencyQuery ()
	{
		if (coOcurrencyQuery==0)
			logCoOcurrencyQuery = 0;
		else
		logCoOcurrencyQuery = Math.log(coOcurrencyQuery);
		//updateMinMax(logCoOcurrencyQuery);
	}
	public double getLogCoOcurrencyQuery ()
	{
		return logCoOcurrencyQuery;
	}
	
	public void setCoOcurrencyQuery(int coOcurrencyQuery, int index) {
		this.coOcurrencyQuery = coOcurrencyQuery;
		//updateMinMax(coOcurrencyQuery);
		featuresVector.put(index,(double) coOcurrencyQuery);
	}

	public void setTf(int tf, int index) {
		this.tf = tf;
		//updateMinMax(tf);
		featuresVector.put(index,(double) tf);
		
	}

	public double getLogDf ()
	{
		return logDf;
	}
	
	public double getLogTf ()
	{
		return logTf;
	}
	
	public double getLogIdf ()
	{
		
		return logIdf;
	}
	
	public void setLogDf (int index)
	{
		if (df == 0)
			logDf = 0;
		else logDf = Math.log(df);
		//updateMinMax(logDf);
		featuresVector.put(index,logDf);
		
		
	}
	
	public void setLogTf (int index)
	{
		if (tf==0)
			logTf = 0;
		else
			logTf = Math.log(tf);
		
		//updateMinMax(logTf);
		featuresVector.put(index,logTf);
		
	}
	
	public void setLogIdf (int index)
	{
		if (idf==0)
			logIdf = 0;
		else
		logIdf = Math.log(idf);
		//updateMinMax(logIdf);
		
		if (logIdf <0)
			logIdf = Math.abs(logIdf);
		featuresVector.put(index,logIdf);
		
	}
	
	public int getDf() {
		return df;
	}

	public void setDf(int df,int index) {
		this.df = df;
		//updateMinMax(df);
		featuresVector.put(index,(double)df);
	}

	public double getIdf() {
		return idf;
	}

	public void setIdf(double idf,int index) {
		this.idf = idf;
		//updateMinMax(idf);
		featuresVector.put(index,idf);
	}
	
	public void setTfIdf (int index)
	{
		tfIdf = tf*idf;
		//updateMinMax(tfIdf);
		featuresVector.put(index,tfIdf);

	}
	public double getTfIdf ()
	{
		
		return (tfIdf);
	}
	
	public void setLogTfIdf (int index)
	{
		if (tfIdf==0)
			logTfIdf = 0;
		else
		logTfIdf = Math.log(tfIdf);
		//updateMinMax(logTfIdf);
		featuresVector.put(index,logTfIdf);
	}
	
	public double getLogTfIdf ()
	{
		return logTfIdf;
	}
	
	public void setLogTfDf (int index)
	{
		if (tf==0 || df == 0)
			logTfDf = 0;
		else
			logTfDf = Math.log(tf*df);
		//updateMinMax(logTfDf);
		featuresVector.put(index,logTfDf);

	}
	public double getLogTfDf ()
	{
		return logTfDf;
	}
	
	public void setTD (double lambda, int index)
	{
		termDependenceScore = lambda*(coOcurrencyQuery+(1-lambda)*pairCoOccurQuery);
		//updateMinMax(termDependenceScore);
		featuresVector.put(index,termDependenceScore);
		
	}
	
	public double getTD ()
	{
		return termDependenceScore;
	}
	
}	
	

