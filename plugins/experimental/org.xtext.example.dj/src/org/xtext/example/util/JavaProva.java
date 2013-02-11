package org.xtext.example.util;

import java.math.BigInteger;
import java.util.*;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.EcoreUtil2;
import org.xtext.example.lookup.AuxiliaryFunctions;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.Class;


public class JavaProva {
	static String name = "";
	static Set<HoldName> holdName = new HashSet<HoldName>();
	
	public static Collection<Config> cConfig(Program p){
		Collection<Config> configurationList = new LinkedList<Config>();
		Collection<Import> importList = new LinkedList<Import>();
		importList.addAll(p.getImports());
		for (Import imp : importList) {
			Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
			Program current = (Program)resource.getContents().get(0);
			if(current.getFeatures() != null){
				configurationList.addAll(current.getFeatures().getConfiguration().getFeatureList());
				break;
			}
		}
		if(configurationList.size() == 0)
			configurationList.addAll(p.getFeatures().getConfiguration().getFeatureList());
		
		return configurationList;
	}
	public static String cConfigName(Program p, Config config){
		return new AuxiliaryFunctions().configurationToString(p, config);
	}
	public static String cFolder(Program p, Config config){
		String name ="";
		Collection<Import> importList = p.getImports();
		if(p.getFeatures() != null){
			name = p.eResource().getURI().lastSegment();
			name = name.substring(0, name.length() - 3);					
		}
		else 
			for(Import imp : importList){
				Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
				Program current = (Program)resource.getContents().get(0);
				if(current.getFeatures() != null){
					name = current.eResource().getURI().lastSegment();
					name = name.substring(0, name.length() - 3);				
				}
			}

		return name;
	}
	
	public static String cPackageName(Program p, Config config){
		String name = cFolder(p, config);
		Collection<Import> importList = p.getImports();
		if(p.getFeatures() != null){
			int i = 0;
			for(Config config2 : p.getFeatures().getConfiguration().getFeatureList()){
				if(config.equals(config2))
					name += "_" + i ;
				i++;
			}						
		}
		else 
			for(Import imp : importList){
				Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
				Program current = (Program)resource.getContents().get(0);
				if(current.getFeatures() != null){
					int i = 0;
					for(Config config2 : current.getFeatures().getConfiguration().getFeatureList()){
						if(config.equals(config2))
						name += "_" + i ;
						i++;
					}						
				}
			}

		return name;
	}
	public static Collection<Class> cClass(Program p, Config config){
		try{
			holdName = new HashSet<HoldName>();
			Collection<Class> classesList = new LinkedList<Class>();
 			Collection<Import> importList = new LinkedList<Import>();
			Collection<Module> moduleList = new LinkedList<Module>();
			Map<BigInteger, Set<Delta>> deltaMapLevel = new AuxiliaryFunctions().deltaLevel(p, config);
			moduleList.addAll(p.getModulesList());
			importList.addAll(p.getImports());
			for (Import imp : importList) {
				Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
				Program current = (Program)resource.getContents().get(0);
				moduleList.addAll(current.getModulesList());
			}
			for (Module m : moduleList){
				if (m.getNtype() != null)
					if (m.getNtype().equals("core"))
						classesList.addAll(m.getCore().getClassesList());
			}
			for (BigInteger b : deltaMapLevel.keySet())
				for (Delta d : deltaMapLevel.get(b))
					for (Classm cm : d.getClassesList())
						if (cm.getAction().equals("adds"))
							classesList.add(cm.getAdds().getClass_());
						else if (cm.getAction().equals("remove"))
							classesList.remove(cm.getRemove().getClass_());
			return classesList;
		} catch (Exception ecc) {
			ecc.printStackTrace();
		}
		return null;
	}
	public static Collection<Method> cMethod(Class classFound, Config config){
		Collection<Method> mlist = new LinkedList<Method>();
		Collection<Object> olist = checkApplicationDeltaMethods(classFound, false, config);
		if(olist != null)
			for(Object o : olist)
				mlist.add((Method)o);
		return mlist;
	}
	public static Collection<ModifiesMethod> cModMethod(Class classFound, Config config){
		holdName = new HashSet<HoldName>();
		Collection<ModifiesMethod> mlist = new LinkedList<ModifiesMethod>();
		Collection<Object> olist = checkApplicationDeltaMethods(classFound, true, config);
		if(olist != null)
			for(Object o : olist)
				mlist.add((ModifiesMethod)o);
		return mlist;
	}
	public static Collection<Field> cField(Class classFound, Config config){
		CST cn = checkApplicationDelta(classFound, config);
		if(cn != null)
			return cn.getFieldList();
		return null;
	}
	public static String cExtends(Class classFound, Config config){
		CST cn = checkApplicationDelta(classFound, config);
		if(cn != null && !cn.getExtending().equals("Object") && !cn.getExtending().equals("")){
			return cn.getExtending();
		}
		return null;
	}
	public static Constructor cConstructor(Class classFound, Config config){
		CST cn = checkApplicationDelta(classFound, config);
		if(cn != null && cn.getConstructor().size() != 0)
			return cn.getConstructor().get(0);
		return null;
	}
	
	public static String cNameMethod(Method method){
		String nameMethod = method.getReference().getName();
		int cont = 0;
		boolean trovato = false;
		for(HoldName hn : holdName){
			if(!trovato && hn.getName().equals(nameMethod)){
				cont = hn.getCont();
				hn.setCont(cont+1);
				trovato = true;
			}		
		}
		if(cont == 0)
			holdName.add(new HoldName(nameMethod, cont +1 ));
		if(cont != 0)
			nameMethod = "___" + nameMethod + "" + cont ;
		return nameMethod;
	}
	public static String cNameModifiesMethod(ModifiesMethod method){
		String nameMethod = method.getMethodRef().getName();
		int cont = 0;
		boolean trovato = false;
		for(HoldName hn : holdName){
			if(!trovato && hn.getName().equals(nameMethod)){
				cont = hn.getCont();
				hn.setCont(cont+1);
				trovato = true;
			}		
		}
		if(cont == 0)
			holdName.add(new HoldName(nameMethod, cont +1));
		if(cont != 0){
			nameMethod = "___" + nameMethod + "" + cont ;
		}
		return nameMethod;
	}
	
	public static String cExpression(Expression ex){
		String expression = "";
		if(ex.getTerminalExpression() != null)
			expression += terminalExpression(ex.getTerminalExpression());
		else if(ex.getReceiver() != null)
			expression = cExpression(ex.getReceiver());
		if(expression.equals("math")){
			if(ex.getMessage() != null && ex.getMessage().getMethodCall() != null){
				MethodCall mc = ex.getMessage().getMethodCall();
				String nm = mc.getName().getName();
				if(nm.equals("add")){
					expression = cExpression(mc.getArgs().get(0).getExpression()) + " + " + cExpression(mc.getArgs().get(1).getExpression());
				}
				else if(nm.equals("sub")){
					expression = cExpression(mc.getArgs().get(0).getExpression()) + " - " + cExpression(mc.getArgs().get(1).getExpression());
				}
				else if(nm.equals("multiply")){
					expression = "(" + cExpression(mc.getArgs().get(0).getExpression()) + ") * (" + cExpression(mc.getArgs().get(1).getExpression()) + ")";
				}
				else if(nm.equals("divide")){
					expression = "(" + cExpression(mc.getArgs().get(0).getExpression()) + ") / (" + cExpression(mc.getArgs().get(1).getExpression()) + ")";
				}
				/*else if(nm.equals("max")){
					expression = mc.getArgs().get(0) + " + " + mc.getArgs().get(1);
				}
				else if(nm.equals("min")){
					expression = mc.getArgs().get(0) + " + " + mc.getArgs().get(1);
				}
				else if(nm.equals("equals")){
					expression = mc.getArgs().get(0) + " + " + mc.getArgs().get(1);
				}
				else if(nm.equals("compare")){
					expression = mc.getArgs().get(0) + " + " + mc.getArgs().get(1);
				}
				else if(nm.equals("abs")){
					expression = mc.getArgs().get(0) + " + " + mc.getArgs().get(1);
				}*/
				else if(nm.equals("not")){
					expression = "-1 * ("  + cExpression(mc.getArgs().get(0).getExpression()) + ")";
				}
			}
		}
		else if(ex.getMessage() != null){
			if(ex.getMessage().getFieldAccess() != null){
				expression += "." + ex.getMessage().getFieldAccess().getName().getName();
			}
			else if (ex.getMessage().getMethodCall() != null){
				expression += "." ;
				expression += ex.getMessage().getMethodCall().getName().getName();
				expression += "(" ;
				int i = 0;
				for(Argument arg : ex.getMessage().getMethodCall().getArgs()){
					expression += cExpression(arg.getExpression()) + ",";
					i++;
				}
				if(i!=0)
					expression = expression.substring(0, expression.length() - 1);
				expression += ")";
			}
		}
		if(ex.getValue() != null)
			expression += " = " + cExpression(ex.getValue());
		return expression;
	}
	
	public static List<String> urisToPackages(Program element) {
		List<Import> uris = element.getImports();
		List<String> imports = new LinkedList<String>();
		
		for(Import uri : uris) {
			imports.add(uriToPackage(uri.getImportURI()));
		}
		
		return imports;
	}
	
	public static String uriToPackage(EObject element) {
		return uriToPackage(element.eResource().getURI().lastSegment());
	}
	
	public static String uriToPackage(String element) {
		int dotIndex = element.lastIndexOf('.');
		return "packages/" + element.substring(0, dotIndex).toLowerCase();
	}
	
	private static String terminalExpression(TerminalExpression te){
		String terminalExpression = "";
		if(te.getCast() != null)
			terminalExpression += "(("+te.getCast().getType().getName() +")"+ cExpression(te.getCast().getExpression()) +")";
		else if(te.getInt() != null)
			terminalExpression += "" + te.getInt().getValue();
		else if(te.getNew() != null){
			if(te.getNew().getType() != null)
				if(("SystemOutWrapper").equals(te.getNew().getType().getName()))
					terminalExpression += "System.out";
				else if(("MyMath").equals(te.getNew().getType().getName()))
				terminalExpression += "math";
				else{
					terminalExpression += "new " + te.getNew().getType().getName() +"(";
					int temp = terminalExpression.length();
					for(Argument arg : te.getNew().getArgs())
						terminalExpression += cExpression(arg.getExpression()) + ",";
					if(terminalExpression.length() > temp)
					terminalExpression = terminalExpression.substring(0, terminalExpression.length() - 1);
					terminalExpression += ")";
				}
			else
				System.err.println("JavaProva Errore non c' tipo");
		}
		else if(te.getNull() != null)
			terminalExpression += "null";
		else if(te.getString() != null)
			terminalExpression += '"' + te.getString().getValue() + '"';
		else if(te.getThis() != null)
			terminalExpression += "this";
		else if(te.getVariable() != null){
			if(te.getVariable().getParameter() != null)
				terminalExpression += te.getVariable().getParameter().getName();
			else
				terminalExpression += te.getVariable().getFieldRef().getName();
		}
		else if(te.getOriginal() != null){
			String nameMethod;
			int cont = 0;
			Method m = new ContainingMethodFinded().lookup(te.getOriginal());
			if(m == null){
				ModifiesMethod mm = new ContainingModifiesMethodFinded().lookup(te.getOriginal());
				nameMethod = mm.getMethodRef().getName();
			}
			else
				nameMethod = m.getReference().getName();
			for(HoldName hn : holdName){
				if(hn.getName().equals(nameMethod)){
					cont = hn.getCont();
					break;
				}
			}
			nameMethod = "___" + nameMethod + "" + cont;
			terminalExpression = nameMethod + "(";
			int temp = terminalExpression.length();
			for(Parameter par : te.getOriginal().getPar())
				terminalExpression += par.getName() + ",";
			if(terminalExpression.length() > temp)
				terminalExpression = terminalExpression.substring(0, terminalExpression.length() -1);
			
			terminalExpression += ")";
				
		}
		return terminalExpression;
	}
	
	private static Collection<Object> checkApplicationDeltaMethods(Class classFound, boolean modifies, Config config){
		CST cn = checkApplicationDelta(classFound, config);
		Collection<Object> cstr = new LinkedList<Object>();
		if(cn != null){
		if(!modifies)
			cstr.addAll(cn.getMethodList());
		else
			cstr.addAll(cn.getModifiesMethodList());
		return cstr;
		}
		return null;
	}
	
	
	private static CST checkApplicationDelta(Class classFound, Config config){
		CST cn = null;
	    try{
	      Module module = new ContainingModuleFinded().lookup(classFound);
	      Program p = new ContainingProgramFinded().lookup(module);
	      Collection<Import> importList = new LinkedList<Import>();
	      Collection<Module> moduleList = new LinkedList<Module>();
	      Map<BigInteger, Set<Delta>> deltaMapLevel = new AuxiliaryFunctions().deltaLevel(p, config);
	      moduleList.addAll(p.getModulesList());
	      importList.addAll(p.getImports());
	      Program current;
	      for (Import imp : importList) {
	        Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	        current = (Program)resource.getContents().get(0);
	        moduleList.addAll(current.getModulesList());
	      }
	      for (Module m : moduleList){
	    	if (m.getNtype() != null)
	        if (m.getNtype().equals("core"))
	          for (Class c : m.getCore().getClassesList()) {
	        	if(c.equals(classFound)){
	        		cn = new CST(c);
	        		if(c.getExtends() == null)
	        			cn.setExtending("Object");
	        	}
	          }
	      }
	      for (BigInteger b : deltaMapLevel.keySet())
	        for (Delta d : deltaMapLevel.get(b))
	          for (Classm cm : d.getClassesList())
	            if (cm.getAction().equals("adds")) {
	              Class c = cm.getAdds().getClass_();
	              if (c.equals(classFound) && cn == null){
	                cn = new CST(c);
	              }
	            }
	            else if (cm.getAction().equals("remove")) {
	              Class c = cm.getRemove().getClass_();
	              if (c.equals(classFound))
	                cn = null;
	            }
	            else if (cm.getAction().equals("modifies")) {
	              Class c = cm.getModifies().getClass_();
	              if (c.equals(classFound))
	                applyModifies(cn, cm.getModifies());
	            }
    	  
	    } catch (Exception ecc) {
	      ecc.printStackTrace();
	    }
	    return cn;
	}
	    
	    private static void applyModifies(CST cn, ModifiesClass mod)
	    {
	  	 try{
  			 Collection<String> removedList = new HashSet<String>();
	  			 for (RemovesMethod rm : mod.getMethod().getRemoveList()) {
	  				 if (cn.containsMethod(rm.getMethodRef().getName())) {
	  					 removedList.add(rm.getMethodRef().getName());
	  				 }
	  			 }

	  			 for (ModifiesMethod mm : mod.getMethod().getModifiesList()) {
	  				 if(cn != null && mm.getMethodRef() != null)
	  					 if (cn.containsMethod(mm.getMethodRef().getName()))
	  						 cn.addModifiesMethod(mm);
	  			 }
	  			 for (AddsMethod am : mod.getMethod().getAddsList()) {
	  				 if (!cn.containsMethod(am.getMethod().getReference().getName()))
	  					 cn.addMethod(am.getMethod());
	  			 }
	  			 for (String name : removedList) {
	  				 cn.removeModifiesMethod(name);
	  				 cn.removeMethod(name);
	  			 }
	  			 removedList.clear();
	  			 for (RemovesField rf : mod.getField().getRemoveList()) {
	  				 if (cn.containsField(rf.getFieldRef().getName())) {
	  					 removedList.add(rf.getFieldRef().getName());
	  				 }
	  			 }
	  			 for (AddsField af : mod.getField().getAddsList()) {
	  				 if (!cn.containsField(af.getField().getReference().getName()))
	  					 cn.addField(af.getField());
	  			 }
	  			 for (String name : removedList)
	  				 cn.removeField(name);
	  			 removedList.clear();
	  			 if(mod.getExtends() != null)
	  				 cn.setExtending(mod.getExtends());
	  				 if(mod.getConstructor() != null)
	  					 cn.setConstructor(mod.getConstructor());
	  	 }catch(Exception ex) {ex.printStackTrace();}
	}
	    
}
