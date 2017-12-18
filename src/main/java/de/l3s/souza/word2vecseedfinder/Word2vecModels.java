package de.l3s.souza.word2vecseedfinder;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.StringTokenizer;

import de.l3s.souza.esfive.ElasticMain;
import de.l3s.souza.esfive.LivingKnowledgeSnapshot;

public class Word2vecModels {

	private static String topicID;
	private static StringBuilder sb;

	public static void main(String args[]) throws IOException {

		walk("/home/souza/NTCIR-eval/ntcir12_Temporalia_taskdata/Evaluation Data");

	}

	@SuppressWarnings("unchecked")
	public static void walk(String path) throws IOException {

		File root = new File(path);
		File[] list = root.listFiles();

		for (File f : list) {
			if (f.isDirectory()) {
				walk(f.getAbsolutePath());

			} else {

				if (!f.getAbsolutePath().contains(".rel"))
					continue;

				File parent = f.getParentFile();

				topicID = parent.getName().toString();
				sb = new StringBuilder();
				BufferedWriter bw = new BufferedWriter(new FileWriter(topicID + ".txt", true));
				;
				FileReader fr = new FileReader(f);
				BufferedReader br = new BufferedReader(fr);

				String line;
				while ((line = br.readLine()) != null) {
					StringTokenizer token = new StringTokenizer(line);
					while (token.hasMoreTokens()) {
						String rel;
						String id;

						id = token.nextToken();
						rel = token.nextToken();
						double relevance;

						if (rel.contentEquals("L0"))
							continue;

						new ElasticMain(id, 1, "id", "souza_livingknowledge");
					//	ElasticMain.run();
						Map<LivingKnowledgeSnapshot, Double> documents = new HashMap<LivingKnowledgeSnapshot, Double>();
						documents = (Map<LivingKnowledgeSnapshot, Double>) ElasticMain.getResults();

						for (Entry<LivingKnowledgeSnapshot, Double> s : documents.entrySet()) {
							// System.out.println((s.getKey().getDocId()));
							sb.append(s.getKey().getText());
						}
					}
				}

				bw.write(sb.toString());
				bw.close();

				System.out.println(topicID + " Done");
			}
		}
	}
}
