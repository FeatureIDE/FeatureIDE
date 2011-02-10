/*    */ package org.xtext.example.util.dotviewer;
/*    */ 
/*    */ import java.awt.Color;
/*    */ import javax.swing.ImageIcon;
/*    */ import javax.swing.JFrame;
import javax.swing.JLabel;
/*    */ 
/*    */ @SuppressWarnings("serial")
/*    */ public class AboutWindow extends JFrame
/*    */ {
/*    */   private JLabel imageLbl;
/*    */ 
/*    */   public AboutWindow()
/*    */   {
/* 13 */     initComponents();
/*    */   }
/*    */ 
/*    */   private void initComponents() {
/* 17 */     this.imageLbl = new JLabel(new ImageIcon("dotviewer/about"));
/* 18 */     this.imageLbl.setBackground(Color.BLACK);
/*    */ 
/* 20 */     add(this.imageLbl);
/* 21 */     setTitle("about");
/*    */ 
/* 23 */     setSize(290, 175);
/*    */   }
/*    */ }

/* Location:           /Users/denis/Desktop/plugins/org.xtext.example.dj2_1.0.0/
 * Qualified Name:     org.xtext.example.util.dotviewer.AboutWindow
 * JD-Core Version:    0.5.4
 */