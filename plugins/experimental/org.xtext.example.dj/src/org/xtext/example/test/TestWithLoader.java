/*     */ package org.xtext.example.test;
/*     */ 
/*     */ import java.io.IOException;
/*     */ import java.util.Collection;
/*     */ import junit.framework.TestCase;
/*     */ import org.eclipse.emf.common.util.EList;
/*     */ import org.eclipse.emf.ecore.EObject;
/*     */ import org.eclipse.emf.ecore.resource.Resource;
/*     */ import org.xtext.example.dJ.Program;
import org.xtext.example.util.ErrorMessage;
/*     */ 
/*     */ public class TestWithLoader extends TestCase
/*     */ {
/*     */   private TestLoader loader;
/*     */ 
/*     */   public TestWithLoader(String name)
/*     */   {
/*  31 */     super(name);
/*     */   }
/*     */ 
/*     */   public void setUp()
/*     */   {
/*  39 */     setLoader(new TestLoader());
/*     */   }
/*     */ 
/*     */   protected void tearDown()
/*     */     throws Exception
/*     */   {
/*  47 */     setLoader(null);
/*     */   }
/*     */ 
/*     */   protected void setLoader(TestLoader fixture)
/*     */   {
/*  55 */     this.loader = fixture;
/*     */   }
/*     */ 
/*     */   protected TestLoader getLoader()
/*     */   {
/*  63 */     return this.loader;
/*     */   }
/*     */ 
/*     */   @SuppressWarnings("rawtypes")
/*     */   protected Program getProgramFromString(String prog, String name)
/*     */     throws IOException
/*     */   {
/*  77 */     Resource resource = getLoader().loadFromString(prog, name);
/*  78 */     EList errors = resource.getErrors();
/*  79 */     if (errors.size() > 0) {
/*  80 */       System.err.println("unexpected errors: " + errors);
/*     */     }
/*     */ 
/*  83 */     assertEquals(0, errors.size());
/*     */ 
/*  85 */     EObject program = (EObject)resource.getContents().get(0);
/*  86 */     return (Program)program;
/*     */   }
/*     */ 
/*     */   protected Program getProgramFromString(String prog)
/*     */     throws IOException
/*     */   {
/*  98 */     return getProgramFromString(prog, "example");
/*     */   }
/*     */ 
/*     */   protected static void printErrors(Collection<ErrorMessage> errorList)
/*     */   {
/* 106 */     System.out.println("ERRORS\n------------------");
/* 107 */     for (ErrorMessage m : errorList)
/* 108 */       System.out.println(m.getMessage());
/* 109 */     System.out.println("------------------");
/*     */   }
/*     */ }
