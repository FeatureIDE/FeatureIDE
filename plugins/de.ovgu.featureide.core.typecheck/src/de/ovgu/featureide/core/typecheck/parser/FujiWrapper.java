package de.ovgu.featureide.core.typecheck.parser;

import java.io.IOException;
import java.util.Iterator;
import java.util.List;

import org.apache.commons.cli.ParseException;

import AST.ClassDecl;
import AST.Program;
import fuji.CompilerWarningException;
import fuji.Composition;
import fuji.FeatureDirNotFoundException;
import fuji.Main;
import fuji.SemanticErrorException;
import fuji.SyntacticErrorException;
import fuji.WrongArgumentException;

/**
 * 
 * @author Sönke Holthusen
 * 
 */
public class FujiWrapper {

	public static boolean hasSuperClass(ClassDecl cl, ClassDecl superclass) {
		if (cl.hasSuperclass()) {
			if (cl.superclass().equals(superclass)) {
				return true;
			} else {
				return hasSuperClass(cl.superclass(), superclass);
			}
		}
		return false;
	}
	
	public static Iterator<Program> getFujiCompositionIterator(List<String> features, String feature_path) throws WrongArgumentException, ParseException, IOException, FeatureDirNotFoundException, SyntacticErrorException, SemanticErrorException, CompilerWarningException
	{
		String[] fuji_options = { "-progmode", "-basedir", feature_path };
		
		Main m = new Main(fuji_options, features);
		
		Composition composition = m.getComposition(m);
		
		return composition.getASTIterator();
	}
}
