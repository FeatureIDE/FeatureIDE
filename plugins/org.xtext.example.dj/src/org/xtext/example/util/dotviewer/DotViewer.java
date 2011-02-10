/*     */ package org.xtext.example.util.dotviewer;
/*     */ 
/*     */ import java.awt.Color;
/*     */ import java.awt.event.ActionEvent;
/*     */ import java.awt.event.ActionListener;
/*     */ import javax.swing.ImageIcon;
/*     */ import javax.swing.JFrame;
/*     */ import javax.swing.JLabel;
/*     */ import javax.swing.JMenu;
/*     */ import javax.swing.JMenuBar;
/*     */ import javax.swing.JMenuItem;
import javax.swing.JPanel;
/*     */ 
/*     */ @SuppressWarnings("serial")
/*     */ public class DotViewer extends JFrame
/*     */ {
/*  15 */   private static int DISP = 60;
/*     */   private JLabel imageLbl;
/*     */   private ImageIcon imageBuffer;
/*     */   private JPanel imagePnl;
/*     */   private JMenuBar menuBar;
/*     */   private JMenu menu;
/*     */   private JMenuItem aboutMenu;
/*     */   private AboutWindow aboutWindow;
/*     */   private String dotBuffer;
/*     */ 
/*     */   public DotViewer(Object dot)
/*     */   {
/*  31 */     if (dot == null) throw new NullPointerException();
/*     */ 
/*  33 */     this.dotBuffer = dot.toString();
/*  34 */     initComponents();
/*     */   }
/*     */   public DotViewer() {
/*  37 */     this.dotBuffer = null;
/*     */   }
/*     */ 
/*     */   private void initComponents()
/*     */   {
/*  42 */     this.imageBuffer = new ImageIcon(DotToByteArray.dotToGif(this.dotBuffer));
/*     */ 
/*  44 */     this.imageLbl = new JLabel(this.imageBuffer);
/*  45 */     this.imageLbl.setBackground(Color.WHITE);
/*     */ 
/*  47 */     this.imagePnl = new JPanel();
/*  48 */     this.imagePnl.setBackground(Color.WHITE);
/*  49 */     this.imagePnl.add(this.imageLbl, "Center");
/*     */ 
/*  52 */     this.aboutMenu = new JMenuItem("About", 65);
/*     */ 
/*  54 */     this.menu = new JMenu("File");
/*  55 */     this.menu.setMnemonic(70);
/*  56 */     this.menu.add(this.aboutMenu);
/*     */ 
/*  58 */     this.menuBar = new JMenuBar();
/*  59 */     this.menuBar.add(this.menu);
/*     */ 
/*  62 */     this.aboutMenu.addActionListener(new ActionListener() {
/*     */       public void actionPerformed(ActionEvent e) {
/*  64 */         DotViewer.this.aboutWindow.setVisible(true);
/*     */       }
/*     */     });
/*  68 */     add(this.menuBar, "North");
/*  69 */     add(this.imagePnl);
/*     */ 
/*  71 */     setTitle("graph view");
/*     */ 
/*  73 */     setSize(this.imageBuffer.getIconWidth() + DISP, 
/*  74 */       this.imageBuffer.getIconHeight() + DISP);
/*     */ 
/*  76 */     this.aboutWindow = new AboutWindow();
/*     */ 
/*  78 */     setVisible(true);
/*     */   }
/*     */ 
/*     */   public void setDot(Object dot)
/*     */   {
/*  84 */     if (dot == null) throw new NullPointerException();
/*     */ 
/*  87 */     if (this.dotBuffer == null) {
/*  88 */       this.dotBuffer = dot.toString();
/*  89 */       initComponents();
/*  90 */       return;
/*     */     }
/*     */ 
/*  93 */     this.dotBuffer = dot.toString();
/*     */ 
/*  95 */     this.imageBuffer = new ImageIcon(DotToByteArray.dotToGif(this.dotBuffer));
/*  96 */     this.imageLbl.setIcon(this.imageBuffer);
/*     */ 
/*  98 */     setSize(this.imageBuffer.getIconWidth() + DISP, 
/*  99 */       this.imageBuffer.getIconHeight() + DISP);
/*     */ 
/* 101 */     setVisible(true);
/*     */   }
/*     */ }

/* Location:           /Users/denis/Desktop/plugins/org.xtext.example.dj2_1.0.0/
 * Qualified Name:     org.xtext.example.util.dotviewer.DotViewer
 * JD-Core Version:    0.5.4
 */