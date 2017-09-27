/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration.action;

import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;

import javax.xml.stream.FactoryConfigurationError;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTConfiguration;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.ModelEditPart;

/**
 * This export implementation is responsible for XML exporting.
 *
 * @author Christopher Kruczek
 */
public class ExportAsXmlImpl extends AbstractExportAsAction {

	public ExportAsXmlImpl(String text, GraphicalViewerImpl view) {
		super(text, view);
	}

	@Override
	public void run() {
		final String file = createXmlSaveDialog().open();
		if (file == null) {
			return;
		}

		try {
			final XMLStreamWriter sw = XMLOutputFactory.newInstance().createXMLStreamWriter(new OutputStreamWriter(new FileOutputStream(file), "UTF-8"));
			sw.writeStartDocument("utf-8", "1.0");
			sw.writeStartElement("configuration");
			final ModelEditPart mep = (ModelEditPart) viewer.getContents();
			for (final Object child : mep.getChildren()) {
				if (child instanceof CollaborationEditPart) {
					final CollaborationEditPart cep = (CollaborationEditPart) child;
					final FSTFeature feature = cep.getCollaborationModel();
					if (!(feature instanceof FSTConfiguration)) {
						writeElement(sw, feature);
					} else {
						sw.writeAttribute("name", feature.getName());
					}
				}
			}
			sw.writeEndElement();
			sw.writeEndDocument();
			sw.flush();
			sw.close();
		} catch (XMLStreamException | FactoryConfigurationError | IOException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	private FileDialog createXmlSaveDialog() {
		final FileDialog dlg = new FileDialog(new Shell(), SWT.SAVE);
		dlg.setFilterExtensions(new String[] { "*.xml" });
		dlg.setOverwrite(true);
		return dlg;
	}

	private void writeElement(XMLStreamWriter writer, FSTFeature feature) {
		try {
			writer.writeStartElement("feature");
			writer.writeAttribute("name", feature.getName());
			for (final FSTRole role : feature.getRoles()) {
				writeElement(writer, role.getClassFragment());
			}
			writer.writeEndElement();
		} catch (final XMLStreamException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	private void writeElement(XMLStreamWriter writer, FSTClassFragment fstClass) {
		try {
			writer.writeStartElement("class");
			writer.writeAttribute("name", fstClass.getName());

			writer.writeStartElement("attributes");
			for (final FSTField field : fstClass.getFields()) {
				writeElement(writer, field);
			}
			writer.writeEndElement();
			writer.writeStartElement("methods");
			for (final FSTMethod method : fstClass.getMethods()) {
				writeElement(writer, method);
			}
			writer.writeEndElement();
			writer.writeEndElement();

		} catch (final XMLStreamException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	private void writeElement(XMLStreamWriter writer, FSTMethod method) {
		try {
			writer.writeStartElement("method");
			writer.writeAttribute(TYPE, method.getType());
			writer.writeAttribute("visibility", method.getModifiers());
			writer.writeCharacters(method.getName());
			writer.writeEndElement();
		} catch (final XMLStreamException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	private void writeElement(XMLStreamWriter writer, FSTField field) {
		try {
			writer.writeStartElement("attribute");
			writer.writeAttribute(TYPE, field.getType());
			writer.writeAttribute("visibility", field.getModifiers());
			writer.writeCharacters(field.getName());
			writer.writeEndElement();
		} catch (final XMLStreamException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

}
