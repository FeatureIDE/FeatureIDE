/*    */ package org.xtext.example.util.dotviewer;
/*    */ 
/*    */ import java.io.ByteArrayOutputStream;
/*    */ import java.io.InputStream;
/*    */ import java.io.OutputStream;
/*    */ import java.io.OutputStreamWriter;
/*    */ import java.io.PrintWriter;
/*    */ 
/*    */ public class DotToByteArray
/*    */ {
/*    */   public static byte[] dotToGif(String dot)
/*    */   {
/* 18 */     Runtime r = Runtime.getRuntime();
/*    */     try
/*    */     {
/* 21 */       Process process = r.exec("/usr/local/bin/dot -Tgif");
/*    */ 
/* 24 */       OutputStream out = process.getOutputStream();
/* 25 */       PrintWriter pw = new PrintWriter(new OutputStreamWriter(out));
/* 26 */       pw.println(dot);
/*    */ 
/* 28 */       pw.flush(); pw.close();
/*    */ 
/* 31 */       InputStream in = process.getInputStream();
/* 32 */       ByteArrayOutputStream ba = new ByteArrayOutputStream();
/*    */ 
/* 34 */       for (int x = in.read(); x != -1; x = in.read()) ba.write(x);
/*    */ 
/* 36 */       ba.flush();
/* 37 */       return ba.toByteArray();
/*    */     } catch (Exception localException) {
/* 39 */       throw new RuntimeException();
/*    */     }
/*    */   }
/*    */ }

/* Location:           /Users/denis/Desktop/plugins/org.xtext.example.dj2_1.0.0/
 * Qualified Name:     org.xtext.example.util.dotviewer.DotToByteArray
 * JD-Core Version:    0.5.4
 */