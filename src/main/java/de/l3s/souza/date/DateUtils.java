package de.l3s.souza.date;

import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.google.protobuf.TextFormat.ParseException;

public class DateUtils {

	public Date convertToDate(String input) throws java.text.ParseException, ParseException {
        Date date = null;
        String format;
        
        if(null == input) {
            return null;
        }
        
          ArrayList<SimpleDateFormat>  dateFormats = new ArrayList<SimpleDateFormat>() {/**
			 * 
			 */
			private static final long serialVersionUID = 1L;

		{
            add(new SimpleDateFormat("M/dd/yyyy"));
            add(new SimpleDateFormat("dd/MM/yyyy"));
            add(new SimpleDateFormat("dd.M.yyyy"));
            add(new SimpleDateFormat("M/dd/yyyy hh:mm:ss a"));
            add(new SimpleDateFormat("dd.M.yyyy hh:mm:ss a"));
            add(new SimpleDateFormat("dd.MMM.yyyy"));
            add(new SimpleDateFormat("dd-MMM-yyyy"));
            add(new SimpleDateFormat("dd-MM-yyyy"));
            add(new SimpleDateFormat("yyyyMMdd"));
//            add(new SimpleDateFormat("yyyy-MM"));
            add(new SimpleDateFormat("yyyy-MM-dd"));
            add(new SimpleDateFormat("dd.MM.yyyy"));
            add(new SimpleDateFormat("yyyy/MM/dd"));
            add(new SimpleDateFormat("yyyy.MM.dd"));
            add(new SimpleDateFormat("yyyy"));
          }
          };
        for (SimpleDateFormat form : dateFormats) {
            form.setLenient(false);
            try {
            	date = form.parse(input);	
            	format = form.toPattern().toString();
            } catch (Exception e)
            {
            	continue;
            }
			
        }
      
        return date;
    }
	
	public String[] getDate(String desc) {
		  int count=0;
		  String[] allMatches = new String[18];
//		  Matcher m = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])[- /.](19)[9]\\d").matcher(desc);
		  //Matcher m = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])[- /.](19)\\d\\d").matcher(desc);
		  Matcher m = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[/](0[1-9]|[12][0-9]|3[01])[/](19)\\d\\d").matcher(desc);
		  Matcher mm1 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[-](0[1-9]|[12][0-9]|3[01])[-](19)\\d\\d").matcher(desc);
		  Matcher mm2 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[.](0[1-9]|[12][0-9]|3[01])[.](19)\\d\\d").matcher(desc);
//		  Matcher m1 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])[- /.](20)[01]\\d").matcher(desc);
		  Matcher m1 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[/](0[1-9]|[12][0-9]|3[01])[/](20)\\d\\d").matcher(desc);
		  //Matcher m1 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])[- /.](20)\\d\\d").matcher(desc);
		  Matcher m11 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[-](0[1-9]|[12][0-9]|3[01])[-](20)\\d\\d").matcher(desc);
		  Matcher m12 = Pattern.compile("(0[1-9]|[12][0-9]|3[01])[.](0[1-9]|[12][0-9]|3[01])[.](20)\\d\\d").matcher(desc);
//		  Matcher m2 = Pattern.compile("(19)[9]\\d[- /.](0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  //Matcher m2 = Pattern.compile("(19)\\d\\d[- /.](0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m2 = Pattern.compile("(19)\\d\\d[/](0[1-9]|[12][0-9]|3[01])[/](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m21 = Pattern.compile("(19)\\d\\d[.](0[1-9]|[12][0-9]|3[01])[.](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m22 = Pattern.compile("(19)\\d\\d[-](0[1-9]|[12][0-9]|3[01])[-](0[1-9]|[12][0-9]|3[01])").matcher(desc);
//		  Matcher m3 = Pattern.compile("(20)[01]\\d[- /.](0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m3 = Pattern.compile("(20)[01]\\d[/](0[1-9]|[12][0-9]|3[01])[/](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m31 = Pattern.compile("(20)[01]\\d[-](0[1-9]|[12][0-9]|3[01])[-](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m32 = Pattern.compile("(20)[01]\\d[.](0[1-9]|[12][0-9]|3[01])[.](0[1-9]|[12][0-9]|3[01])").matcher(desc);
		//  Matcher m3 = Pattern.compile("(20)\\d\\d[- /.](0[1-9]|[12][0-9]|3[01])[- /.](0[1-9]|[12][0-9]|3[01])").matcher(desc);
//		  Matcher m4 = Pattern.compile("(19)[9]\\d(0[1-9]|[12][0-9]|3[01])(0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  //Matcher m4 = Pattern.compile("(19)\\d\\d(0[1-9]|[12][0-9]|3[01])(0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m4 = Pattern.compile("(19)\\d\\d(0[1-9]|[12][0-9]|3[01])(0[1-9]|[12][0-9]|3[01])").matcher(desc);
//		  Matcher m5 = Pattern.compile("(20)[01]\\d(0[1-9]|[12][0-9]|3[01])(0[1-9]|[12][0-9]|3[01])").matcher(desc);
		  Matcher m5 = Pattern.compile("(20)\\d\\d(0[1-9]|[12][0-9]|3[01])(0[1-9]|[12][0-9]|3[01])").matcher(desc);
//		  Matcher m6 = Pattern.compile("(19)[9]\\d[- /.](0[1-9]|[12][0-9])").matcher(desc);
		  Matcher m6 = Pattern.compile("(19)\\d\\d[/](0[1-9]|[12][0-9])").matcher(desc);
		  Matcher m61 = Pattern.compile("(19)\\d\\d[-](0[1-9]|[12][0-9])").matcher(desc);
		  Matcher m62 = Pattern.compile("(19)\\d\\d[.](0[1-9]|[12][0-9])").matcher(desc);
//		  Matcher m7 = Pattern.compile("(20)[01]\\d[- /.](0[1-9]|[12][0-9])").matcher(desc);
/*		  Matcher m7 = Pattern.compile("(20)\\d\\d[/](0[1-9]|[12][0-9])").matcher(desc);
		  Matcher m71 = Pattern.compile("(20)\\d\\d[-](0[1-9]|[12][0-9])").matcher(desc);
		  Matcher m72 = Pattern.compile("(20)\\d\\d[.](0[1-9]|[12][0-9])").matcher(desc);*/
		//  Matcher m8 = Pattern.compile("(20)\\d\\d").matcher(desc);
		  
		  if (m.find()) {
		    allMatches[count] = m.group();
		    count ++;
		  }
		  
		  if (mm1.find()) {
			    allMatches[count] = mm1.group();
			    count ++;
			  }
		  if (mm2.find()) {
			    allMatches[count] = mm2.group();
			    count ++;
			  }
		  if (m11.find()) {
			    allMatches[count] = m11.group();
			    count ++;
			  }
		  if (m12.find()) {
			    allMatches[count] = m12.group();
			    count ++;
			  }
		  if (m21.find()) {
			    allMatches[count] = m21.group();
			    count ++;
			  }
		  if (m22.find()) {
			    allMatches[count] = m22.group();
			    count ++;
			  }
		  
		  if (m61.find()) {
			    allMatches[count] = m61.group();
			    count ++;
			  }
		  if (m62.find()) {
			    allMatches[count] = m62.group();
			    count ++;
			  }
	/*	  if (m71.find()) {
			    allMatches[count] = m71.group();
			    count ++;
			  }
		  
		  if (m72.find()) {
			    allMatches[count] = m72.group();
			    count ++;
			  }*/
		  if (m31.find()) {
			    allMatches[count] = m31.group();
			    count ++;
			  }
		  if (m32.find()) {
			    allMatches[count] = m32.group();
			    count ++;
			  }
		  if (m.find()) {
			    allMatches[count] = m.group();
			    count ++;
			  }
		  if (m1.find()) {
			    allMatches[count] = m1.group();
			    count ++;
		  }
		  
		  if (m2.find()) {
			    allMatches[count] = m2.group();
			    count ++;
			    
			  }
		  
		  if (m3.find()) {
			    allMatches[count] = m3.group();
			    count ++;
			    
			  }
		  if (m4.find()) {
			  	
			    allMatches[count] = m4.group();
			    count ++;
		  }
		  if (m5.find()) {
			  	
			    allMatches[count] = m5.group();
			    count ++;
		  }
		  if (m6.find()) {
			  	
			    allMatches[count] = m6.group();
			    count ++;
		  }
		  
		/*  if (m7.find()) {
			  	
			    allMatches[count] = m7.group();
			    count ++;
		  }*/
		  
		/*  if (m8.find()) {
			    allMatches[count] = m8.group();
			    count ++;
			  }*/
		  
		  return allMatches;
		}
	
	public static Date parseDate(String date_str) {
        SimpleDateFormat df = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
        SimpleDateFormat df1 = new SimpleDateFormat("yyyy/MM/dd");
        SimpleDateFormat df2 = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
        SimpleDateFormat df11 = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
        SimpleDateFormat df3 = new SimpleDateFormat("EEE, MMM d, yyyy");
        SimpleDateFormat df4 = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss.SSSZ");
        SimpleDateFormat df5 = new SimpleDateFormat("EEE, MMM. dd, yyyy");
        SimpleDateFormat df6 = new SimpleDateFormat("EEE, MMM dd, yyyy");
        SimpleDateFormat df7 = new SimpleDateFormat("yyyyMMdd");
        SimpleDateFormat df8 = new SimpleDateFormat("EEEEE d MMM yyyy");
        SimpleDateFormat df9 = new SimpleDateFormat("EEEEE, MMM. dd, yyyy");
        SimpleDateFormat df10 = new SimpleDateFormat("dd MMM yyyy");
        SimpleDateFormat df12 = new SimpleDateFormat("MMM dd, yyyy, HH:mm a");
        SimpleDateFormat df14 = new SimpleDateFormat("MMM dd, yyyy, H:mm a");
        SimpleDateFormat df13 = new SimpleDateFormat("dd.MM.yyyy");
        SimpleDateFormat df15 = new SimpleDateFormat("MMMMM dd, yyyy, HH:mm a");
        SimpleDateFormat df16 = new SimpleDateFormat("MMMMM dd, yyyy, H:mm a");
        SimpleDateFormat df17 = new SimpleDateFormat("MMM. dd, yyyy");
       
        SimpleDateFormat df18 = new SimpleDateFormat("MMMMM dd, yyyy");
        SimpleDateFormat df19 = new SimpleDateFormat("EEEEE, MMM. dd, yyyy");
        SimpleDateFormat df_20 = new SimpleDateFormat("EEE, dd MMM yyyy HH:mm:ss z");
        SimpleDateFormat df21 = new SimpleDateFormat("MMMM dd, yyyy");
        SimpleDateFormat df22 = new SimpleDateFormat("MMMM dd, yyyy HH:mm a");
        SimpleDateFormat df23 = new SimpleDateFormat("EEE MMMM dd HH:mm:ss z yyyy");
        SimpleDateFormat df24 = new SimpleDateFormat("dd/MM/yyyy");
        SimpleDateFormat df25 = new SimpleDateFormat("dd-MM-yyyy");
        SimpleDateFormat df26 = new SimpleDateFormat("MMM dd, yyyy Z H:mm");
        List<SimpleDateFormat> lst = new ArrayList<SimpleDateFormat>();
        lst.add(df);
        lst.add(df1);
        lst.add(df2);
        lst.add(df3);
        lst.add(df4);
        lst.add(df5);
        lst.add(df6);
        lst.add(df7);
        lst.add(df8);
        lst.add(df9);
        lst.add(df10);
        lst.add(df11);
        lst.add(df12);
        lst.add(df13);
        lst.add(df14);
        lst.add(df15);
        lst.add(df16);
        lst.add(df17);
        lst.add(df18);
        lst.add(df19);
        lst.add(df_20);
        lst.add(df21);
        lst.add(df22);
        lst.add(df23);
        lst.add(df24);
        lst.add(df25);
        lst.add(df26);
        //SimpleDateFormat df_simple = new SimpleDateFormat("yyyyMMddHHmmss");
        for (SimpleDateFormat df_tmp : lst) {
            try {
                Date dt = df_tmp.parse(date_str);
                return dt;
            } catch (Exception e) {
                continue;
            }
        }
        Date date = new Date ();
        return date;

    }
}
