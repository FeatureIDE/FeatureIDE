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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.ClassFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.UnderlayerFigure;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;
import de.ovgu.featureide.ui.views.collaboration.policy.ClassXYLayoutPolicy;

/**
 * EditPart of all graphical objects, resize and relocate all editParts of collaboration diagram {@link #refreshVisuals()}
 *
 * @author Constanze Adler
 * @author Steffen Schulze
 * @author Christian Lausberger
 */
public class ModelEditPart extends AbstractGraphicalEditPart implements GUIDefaults {

	private final LinkedList<CollaborationEditPart> collaborationEditPartList = new LinkedList<CollaborationEditPart>();
	private final LinkedList<ClassEditPart> classEditPartList = new LinkedList<ClassEditPart>();

	/**
	 * Defines the order of classes displayed at the collaboration view.
	 */
	private static final Comparator<? super FSTClass> CLASS_COMPARATOR = new Comparator<FSTClass>() {

		@Override
		public int compare(final FSTClass class1, final FSTClass class2) {
			final String name1 = class1.getName();
			final boolean isArbitrary1 = name1.startsWith("*");
			final String name2 = class2.getName();
			final boolean isArbitrary2 = name2.startsWith("*");
			if (!isArbitrary1 && !isArbitrary2) {
				final boolean class1Empty = class1.getRoles().isEmpty();
				final boolean class2Empty = class2.getRoles().isEmpty();
				if (class1Empty && !class2Empty) {
					return 1;
				} else if (!class1Empty && class2Empty) {
					return -1;
				}
				return name1.compareToIgnoreCase(name2);
			} else if (isArbitrary1 && isArbitrary2) {
				return name1.compareToIgnoreCase(name2);
			} else {
				if (isArbitrary1) {
					return 1;
				} else {
					return -1;
				}
			}
		}
	};

	public ModelEditPart(FSTModel model) {
		setModel(model);
	}

	public FSTModel getCollaborationModel() {
		return (FSTModel) getModel();
	}

	@Override
	protected IFigure createFigure() {
		final Figure fig = new FreeformLayer();
		fig.setLayoutManager(new FreeformLayout());
		fig.setBorder(new MarginBorder(10));
		fig.setBackgroundColor(GUIDefaults.DIAGRAM_BACKGROUND);
		return fig;
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ClassXYLayoutPolicy());
	}

	@Override
	protected List<?> getModelChildren() {
		final FSTModel model = getCollaborationModel();
		final List<Object> list = new LinkedList<Object>();
		addCollaborations(model, list);
		addClasses(model.getClasses(), list);
		return list;
	}

	private void addCollaborations(final FSTModel model, final Collection<Object> list) {
		list.add(model.getConfiguration());
		final IFeatureProject featureProject = model.getFeatureProject();
		if (featureProject != null) {
			for (final String feature : featureProject.getFeatureModel().getFeatureOrderList()) {
				final FSTFeature f = model.addFeature(feature);
				if (CollaborationModelBuilder.showFeature(f)) {
					list.add(f);
				}
			}
		}
	}

	private void addClasses(final List<FSTClass> classes, final List<Object> list) {
		Collections.sort(classes, CLASS_COMPARATOR);
		for (final FSTClass c : classes) {
			if (CollaborationModelBuilder.showClass(c)) {
				list.add(c);
			}
		}
	}

	@Override
	protected void removeChildVisual(EditPart childEditPart) {
		super.removeChildVisual(childEditPart);
		if (childEditPart instanceof CollaborationEditPart) {
			collaborationEditPartList.remove(childEditPart);
		} else if (childEditPart instanceof ClassEditPart) {
			classEditPartList.remove(childEditPart);
		}
	}

	@Override
	protected void addChildVisual(EditPart childEditPart, int index) {
		super.addChildVisual(childEditPart, index);
		if (childEditPart instanceof CollaborationEditPart) {
			collaborationEditPartList.add((CollaborationEditPart) childEditPart);
		} else if (childEditPart instanceof ClassEditPart) {
			classEditPartList.add((ClassEditPart) childEditPart);
		}
	}

	@Override
	protected void refreshVisuals() {
		if (children == null) {
			return;
		}

		final Map<String, Integer> heightsMap = getMapForCollaborationFigureHeights();
		final int collFigureWidth = getWidthForCollaborationFigures();

		CollaborationEditPart lastCollaborationEditPart = null;
		for (final CollaborationEditPart collaborationEditPart : collaborationEditPartList) {
			final UnderlayerFigure underlayer = (UnderlayerFigure) collaborationEditPart.getFigure();
			// set height of Collaboration Figures
			setHeightForCollaborationFigures(heightsMap, collaborationEditPart, lastCollaborationEditPart);
			// set width of Underlayer Figure
			underlayer.setCollaborationFigureWidth(collFigureWidth);

			final List<?> list = getModelChildren();
			final FSTFeature coll = (FSTFeature) list.get(collaborationEditPartList.indexOf(collaborationEditPart));
			// set default background color of underlayerFigure
			if (coll.getColor() == -1) {
				if ((collaborationEditPartList.indexOf(collaborationEditPart) % 2) == 0) {
					underlayer.setBackgroundColor(DEFAULT_UNDERLAYING_COLOR_1);
				} else {
					underlayer.setBackgroundColor(DEFAULT_UNDERLAYING_COLOR_2);
				}
			}

			lastCollaborationEditPart = collaborationEditPart;
		}

		ClassEditPart lastClassEditPart = null;
		for (final ClassEditPart classEditPart : classEditPartList) {
			// find max width of roleFigures
			final RoleFigure figure = getMaxWidthRoleFigure(classEditPart);
			if (figure != null) {
				int width = figure.getBounds().width;
				if (width == 0) {
					width = classEditPart.getFigure().getBounds().width - CLASS_INSETS.left;
				}
				// set width for ClassFigure
				setWidthForClassFigure(width, classEditPart);

				// set width for all roleFigures
				setWidthForRoleFigures(width, classEditPart);
			}
			// set Location
			setLocationForClassFigure(classEditPart, lastClassEditPart);
			setLocationForRoleFigures(classEditPart);
			// set Height
			setHeightForClassFigure(getHeightForClassFigures(heightsMap), classEditPart);
			setHeightForRoleFigures(classEditPart);

			lastClassEditPart = classEditPart;
		}

		for (final CollaborationEditPart collaborationEditPart : collaborationEditPartList) {
			setWidthForCollaborationFigure(collFigureWidth, collaborationEditPart);
		}
	}

	private void setHeightForRoleFigures(ClassEditPart classEdit) {
		for (final Object child : classEdit.getChildren()) {
			if (child instanceof RoleEditPart) {
				final RoleEditPart roleEditPart = (RoleEditPart) child;

				final RoleFigure figure = (RoleFigure) roleEditPart.getFigure();
				if (figure.getChildren().size() > 0) {
					final Dimension size = getConstraintForFigure(figure).getSize();
					for (final UnderlayerFigure ulf : getUnderlayerFigure(roleEditPart)) {
						final CollaborationFigure colFigure = ulf.getCollaborationFigure();
						final Rectangle constraintCollaboration = getConstraintForFigure(colFigure);
						int height = size.height;
						final int alterHeight = constraintCollaboration.height;
						if (height < alterHeight) {
							height = alterHeight;
							size.height = height;
							final Rectangle constraint = new Rectangle(figure.getLocation(), size);

							classEdit.setLayoutConstraint(this, figure, constraint);
							figure.setBounds(constraint);
						}
					}
				}
			}
		}
	}

	private void setHeightForCollaborationFigures(Map<String, Integer> heightMap, CollaborationEditPart collaborationEditPart,
			CollaborationEditPart lastCollaborationEditPart) {
		if (lastCollaborationEditPart != null) {
			final Rectangle constraint = getConstraintForEditPart(lastCollaborationEditPart);
			String name = ((FSTFeature) lastCollaborationEditPart.getModel()).getName();
			final Rectangle rect = new Rectangle(constraint);

			int yValue = constraint.height + 4;

			if (heightMap.containsKey(name)) {
				final int alterYValue = heightMap.get(name) + 4;
				if (yValue < alterYValue) {
					yValue = alterYValue;
				}
			}
			yValue += constraint.y;

			rect.y = yValue;

			name = ((FSTFeature) collaborationEditPart.getModel()).getName();
			int height = ((UnderlayerFigure) (collaborationEditPart.getFigure())).getCollaborationFigure().getBounds().height;
			if (heightMap.containsKey(name)) {
				height = Math.max(height, heightMap.get(name)) + 12;
			} else {
				height += 12;
			}
			rect.height = height;

			setLayoutConstraint(collaborationEditPart, collaborationEditPart.getFigure(), rect);
		}
	}

	private RoleFigure getMaxWidthRoleFigure(ClassEditPart editPart) {
		RoleFigure maxFigure = null;
		for (final Object child : editPart.getChildren()) {
			if (child instanceof RoleEditPart) {
				final RoleEditPart roleEditPart = (RoleEditPart) child;

				final RoleFigure figure = (RoleFigure) roleEditPart.getFigure();

				if ((maxFigure == null) || (maxFigure.getBounds().width < figure.getBounds().width)) {
					maxFigure = figure;
				}
			}
		}

		return maxFigure;
	}

	private void setWidthForRoleFigures(int width, ClassEditPart editPart) {
		for (final Object child : editPart.getChildren()) {
			if (child instanceof RoleEditPart) {
				final RoleEditPart roleEditPart = (RoleEditPart) child;

				final RoleFigure figure = (RoleFigure) roleEditPart.getFigure();

				final Dimension size = getConstraintForFigure(figure).getSize();
				size.width = width;
				final Rectangle constraint = new Rectangle(figure.getLocation(), size);

				editPart.setLayoutConstraint(this, figure, constraint);
				figure.setBounds(constraint);

				for (final Object o : figure.getChildren()) {
					if (o instanceof Panel) {
						((Panel) o).setBounds(constraint);
					}
				}
			}

		}
	}

	private void setWidthForClassFigure(int width, ClassEditPart editPart) {
		final ClassFigure figure = (ClassFigure) editPart.getFigure();
		final Dimension size = figure.getSize();
		final Rectangle constraintClass = getConstraintForEditPart(editPart);

		if (width > (size.width - (CLASS_INSETS.left))) {
			size.width = width + CLASS_INSETS.left;

			constraintClass.setSize(size);

			setLayoutConstraint(this, figure, constraintClass);
			figure.setBounds(constraintClass);
		}
		for (final Object o : figure.getChildren()) {
			if (o instanceof Label) {
				final Rectangle rect = ((Label) o).getBounds();
				final int xValue = constraintClass.getLocation().x + ((constraintClass.width - rect.width) / 2);
				rect.x = xValue;
			}
		}
	}

	private void setLocationForClassFigure(GraphicalEditPart editPart, GraphicalEditPart lastEditPart) {
		final IFigure figure = editPart.getFigure();
		final Rectangle constraintClass = getConstraintForEditPart(editPart);

		Rectangle constraintPreClass;
		if (lastEditPart == null) {
			constraintPreClass = getConstraintForFigure(((UnderlayerFigure) collaborationEditPartList.getLast().getFigure()).getCollaborationFigure());
		} else {
			constraintPreClass = getConstraintForEditPart(lastEditPart);
		}

		final int xValue = constraintPreClass.getLocation().x + constraintPreClass.width + GENERAL_DISTANCE;
		constraintClass.x = xValue;

		setLayoutConstraint(this, figure, constraintClass);
		figure.setBounds(constraintClass);
	}

	private void setLocationForRoleFigures(ClassEditPart editPart) {

		for (final Object o : editPart.getChildren()) {
			final RoleEditPart roleEditPart = (RoleEditPart) o;
			final RoleFigure figure = (RoleFigure) (roleEditPart).getFigure();
			final Rectangle constraintClass = getConstraintForEditPart(editPart);
			final Rectangle constraintRole = figure.getBounds();
			final List<UnderlayerFigure> ulFigure = getUnderlayerFigure(roleEditPart);

			for (final UnderlayerFigure ulf : ulFigure) {
				final Rectangle constraintCollaboration = getConstraintForFigure(ulf);
				final int nY = ulf.getCollaborationFigure().getLocation().y - ulf.getLocation().y;
				final int xValue = constraintClass.getLocation().x + ((constraintClass.width - constraintRole.width) / 2);
				final int yValue = constraintCollaboration.getLocation().y + nY;
				constraintRole.x = xValue;
				constraintRole.y = yValue;
				setLayoutConstraint(this, figure, constraintRole);
				figure.setBounds(constraintRole);

				for (final Object child : figure.getChildren()) {
					if (child instanceof Panel) {
						((Panel) child).setBounds(constraintRole);
					}
				}
			}
		}
	}

	private Map<String, Integer> getMapForCollaborationFigureHeights() {
		final Map<String, Integer> map = new HashMap<String, Integer>();
		for (final ClassEditPart classEditPart : classEditPartList) {
			for (final Object o : classEditPart.getChildren()) {
				if (o instanceof RoleEditPart) {
					final RoleEditPart roleEdit = (RoleEditPart) o;
					final RoleFigure roleFigure = (RoleFigure) roleEdit.getFigure();
					final String name = roleFigure.getRole().getFeature().toString();

					final int height = roleFigure.getBounds().height;

					if (map.containsKey(name)) {
						if (map.get(name) < height) {
							map.put(name, height);
						}
					} else {
						map.put(name, height);
					}
				}
			}
		}
		return map;
	}

	private Rectangle getConstraintForEditPart(GraphicalEditPart editPart) {
		final Figure partFigure = (Figure) editPart.getFigure();

		return getConstraintForFigure(partFigure);
	}

	private Rectangle getConstraintForFigure(IFigure partFigure) {
		final Rectangle rect = (Rectangle) getFigure().getLayoutManager().getConstraint(partFigure);
		if (rect != null) {
			return rect;
		}

		return new Rectangle(partFigure.getBounds());
	}

	private List<UnderlayerFigure> getUnderlayerFigure(RoleEditPart editPart) {
		final FSTFeature feature = editPart.getRoleModel().getFeature();
		final List<UnderlayerFigure> ulFigures = new LinkedList<UnderlayerFigure>();
		for (final CollaborationEditPart part : collaborationEditPartList) {
			if (feature.getName().contains(part.getModel().toString()) && feature.getRoles().equals(part.getCollaborationModel().getRoles())) {
				ulFigures.add((UnderlayerFigure) part.getFigure());
			}
		}

		return ulFigures;
	}

	private int getHeightForClassFigures(Map<String, Integer> heightMap) {
		final CollaborationEditPart part = collaborationEditPartList.getLast();

		final Rectangle rect = getConstraintForEditPart(part);
		final String name = ((FSTFeature) part.getModel()).getName();

		int height = rect.y + rect.height + COLLABORATION_INSETS.top;

		if (heightMap.containsKey(name)) {
			final int alterHeight = rect.y + heightMap.get(name) + COLLABORATION_INSETS.top;
			if (height < alterHeight) {
				height = alterHeight;
			}
		}

		return height;
	}

	private void setHeightForClassFigure(int height, GraphicalEditPart editPart) {
		final Rectangle rect = getConstraintForEditPart(editPart);
		rect.height = height;
		final IFigure figure2 = editPart.getFigure();
		setLayoutConstraint(this, figure2, rect);
		figure2.setBounds(rect);
	}

	private int getWidthForCollaborationFigures() {
		int width = 0;
		for (final CollaborationEditPart collaborationEditPart : collaborationEditPartList) {
			final UnderlayerFigure ulFigure = (UnderlayerFigure) collaborationEditPart.getFigure();
			width = (width > ulFigure.getCollaborationFigureWidth()) ? width : ulFigure.getCollaborationFigureWidth();
		}
		return width;
	}

	private void setWidthForCollaborationFigure(int width, CollaborationEditPart editPart) {
		final Rectangle ulConstraint = new Rectangle(getConstraintForEditPart(editPart));
		if (!classEditPartList.isEmpty()) {
			final Rectangle lastClassConstraint = getConstraintForEditPart(classEditPartList.getLast());
			width = (lastClassConstraint.x + lastClassConstraint.width) - ulConstraint.x;
		} else {
			width += COLLABORATION_INSETS.right;
		}

		ulConstraint.width = width + COLLABORATION_INSETS.right;
		setLayoutConstraint(this, editPart.getFigure(), ulConstraint);
	}
}
