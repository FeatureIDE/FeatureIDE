/*     */ package org.xtext.example.test;
/*     */ 
/*     */ import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.mwe.utils.StandaloneSetup;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import org.xtext.example.DJStandaloneSetup;
import org.xtext.example.dJ.Program;

import com.google.inject.Injector;
/*     */ 
/*     */ public class TestLoader
/*     */ {
/*  25 */   private Injector injector = new DJStandaloneSetup()
/*  25 */     .createInjectorAndDoEMFRegistration();
/*     */   private XtextResourceSet resourceSet;
/*     */ 
/*     */   public TestLoader()
/*     */   {
/*  33 */     new StandaloneSetup().setPlatformUri("../");
/*     */ 
/*  35 */     this.resourceSet = ((XtextResourceSet)this.injector.getInstance(XtextResourceSet.class));
/*  36 */     this.resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, 
/*  37 */       Boolean.TRUE);
/*     */   }
/*     */ 
/*     */   public Resource createResource()
/*     */   {
/*  45 */     return this.resourceSet.createResource(URI.createURI("http:///My.dj"));
/*     */   }
/*     */ 
/*     */   public Resource loadResource(String programName)
/*     */   {
/*  54 */     return this.resourceSet.getResource(
/*  55 */       URI.createURI("platform:/resource/org.xtext.example.test/" + 
/*  56 */       programName), true);
/*     */   }
/*     */ 
/*     */   public Resource loadFromString(String program, String name)
/*     */     throws IOException
/*     */   {
/*  68 */     Resource resource = this.resourceSet.createResource(
/*  69 */       URI.createURI("dummy:/" + name + ".dj"));
/*  70 */     InputStream in = new ByteArrayInputStream(program.getBytes());
/*  71 */     System.out.print(resource);
/*  72 */     resource.load(in, this.resourceSet.getLoadOptions());
/*  73 */     return resource;
/*     */   }
/*     */ 
/*     */   public Program loadProgramFromString(String program, String name)
/*     */     throws IOException
/*     */   {
/*  85 */     return (Program)loadFromString(program, name).getContents().get(0);
/*     */   }
/*     */ 
/*     */   public Program loadProgramFromString(String program)
/*     */     throws IOException
/*     */   {
/*  95 */     return loadProgramFromString(program, "example");
/*     */   }
/*     */ 
/*     */   public static void main(String[] args)
/*     */     throws IOException
/*     */   {
/* 103 */     TestLoader loader = new TestLoader();
/* 104 */     loader.loadProgramFromString("core Base{}");
/*     */   }
/*     */ }
