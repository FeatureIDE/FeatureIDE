/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration.action;

import java.util.Collection;

import javax.xml.stream.XMLStreamWriter;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.ModelEditPart;


/**
 * This export implementation is responsible for XML exporting.
 * 
 * @author Christopher Kruczek
 */
public class ExportAsXmlImpl implements ExportAsImplemenation {

	
	@Override
	public void export(GraphicalViewerImpl viewer) {
		
		String file = createXmlSaveDialog().open();

	}
	
	private FileDialog createXmlSaveDialog(){
		FileDialog dlg = new FileDialog(new Shell(), SWT.SAVE);
		dlg.setFilterExtensions(new String[]{"*.xml"});
		return dlg;
	}
	
	private void writeElement(XMLStreamWriter writer,FSTFeature feature){
	}
	
	private void writeElement(XMLStreamWriter writer, FSTClass fstClass){
		
	}
	
	private void writeElement(XMLStreamWriter writer, FSTMethod method){
		
	}
	
	private void writeElement(XMLStreamWriter writer,FSTField field){
		
	}
	
	

}
