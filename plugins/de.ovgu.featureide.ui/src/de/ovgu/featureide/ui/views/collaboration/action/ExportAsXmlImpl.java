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

import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;

import javax.xml.stream.FactoryConfigurationError;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;

import org.eclipse.gef.editparts.AbstractEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.ModelEditPart;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;

/**
 * This export implementation is responsible for XML exporting.
 * 
 * @author Christopher Kruczek
 */
public class ExportAsXmlImpl implements ExportAsImplemenation {

	@Override
	public void export(GraphicalViewerImpl viewer) {

		String file = createXmlSaveDialog().open();
		if (file == null)
			return;

		XMLStreamWriter sw;
		try {
			sw = XMLOutputFactory.newInstance().createXMLStreamWriter(
					new FileWriter(file));
			sw.writeStartDocument("utf-8", "1.0");
			sw.writeStartElement("configuration");
			ModelEditPart mep = (ModelEditPart) viewer.getContents();
			for (Object child : mep.getChildren()) {
				if (child instanceof CollaborationEditPart) {
					CollaborationEditPart cep = (CollaborationEditPart) child;
					writeElement(sw, cep.getCollaborationModel());
				}
			}
			sw.writeEndElement();
			sw.writeEndDocument();
			sw.flush();
			sw.close();
		} catch (XMLStreamException e) {

			e.printStackTrace();
		} catch (FactoryConfigurationError e) {

			e.printStackTrace();
		} catch (IOException e) {

			e.printStackTrace();
		}

	}

	private FileDialog createXmlSaveDialog() {
		FileDialog dlg = new FileDialog(new Shell(), SWT.SAVE);
		dlg.setFilterExtensions(new String[] { "*.xml" });
		dlg.setOverwrite(true);
		return dlg;
	}

	private void writeElement(XMLStreamWriter writer, FSTFeature feature) {
		try {
			writer.writeStartElement("feature");
			writer.writeAttribute("name", feature.getName());
			for (FSTRole role : feature.getRoles()) {
				writeElement(writer, role.getClassFragment());
			}
			writer.writeEndElement();

		} catch (XMLStreamException e) {

			e.printStackTrace();
		}

	}

	private void writeElement(XMLStreamWriter writer, FSTClassFragment fstClass) {
		try {
			writer.writeStartElement("class");
			writer.writeAttribute("name", fstClass.getName());

			writer.writeStartElement("attributes");
			for (FSTField field : fstClass.getFields()) {
				writeElement(writer, field);
			}
			writer.writeEndElement();
			writer.writeStartElement("methods");
			for (FSTMethod method : fstClass.getMethods()) {
				writeElement(writer, method);
			}
			writer.writeEndElement();

			writer.writeEndElement();

		} catch (XMLStreamException e) {

			e.printStackTrace();
		}

	}

	private void writeElement(XMLStreamWriter writer, FSTMethod method) {
		try {
			writer.writeStartElement("method");
			writer.writeCharacters(method.getName());
			writer.writeEndElement();
		} catch (XMLStreamException e) {

			e.printStackTrace();
		}

	}

	private void writeElement(XMLStreamWriter writer, FSTField field) {
		try {
			writer.writeStartElement("attribute");
			writer.writeCharacters(field.getName());
			writer.writeEndElement();
		} catch (XMLStreamException e) {

			e.printStackTrace();
		}

	}

}
