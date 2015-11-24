/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.HotSpotResult;
import de.ovgu.featureide.fm.core.IHotSpotResultInterpreter;

/**
 * TODO description
 * 
 * @author Christopher Kruczek
 * @author Andy Kenner
 */
public class ColorMetricHotSpotInterpreter implements IHotSpotResultInterpreter<Color> {

	private static final Display display = Display.getCurrent();
	private static final Color[] scalaColor = new Color[] {
			// clear green
			new Color(display, 0, 150, 0),
			// Yellow
			new Color(display, 255, 255, 0),
			// Red
			new Color(display, 255, 0, 0), };
	private Color[] scale;
	private int maxRange;

	public ColorMetricHotSpotInterpreter(int maxRange) {
		this.maxRange = maxRange;
		this.init();
	}

	private void init() {

		if (maxRange < 3) {
			 if(maxRange < 1) {
				 /*TODO*/
				 System.out.println("SHIT");
				 return;
			 }
			 
			this.scale = new Color[this.maxRange];
			if (maxRange == 1) 
			{
				this.scale[0] = ColorMetricHotSpotInterpreter.scalaColor[2];
			} 
			else if (maxRange == 2)
			{
				this.scale[0] = ColorMetricHotSpotInterpreter.scalaColor[0];
				this.scale[1] = ColorMetricHotSpotInterpreter.scalaColor[2];
			}
		}

		else {

			this.scale = new Color[this.maxRange];
			this.scale[0] = ColorMetricHotSpotInterpreter.scalaColor[0];
			//int substracter = (maxRange/2) % 2 == 0 ? 1 : 0;
			int stepWidth = (maxRange / 2) - 1;

			double rChange = (ColorMetricHotSpotInterpreter.scalaColor[1].getRed() - ColorMetricHotSpotInterpreter.scalaColor[0].getRed()) / (stepWidth + 1);
			double gChange = (ColorMetricHotSpotInterpreter.scalaColor[1].getGreen() - ColorMetricHotSpotInterpreter.scalaColor[0].getGreen())
					/ (stepWidth + 1);
			double bChange = (ColorMetricHotSpotInterpreter.scalaColor[1].getBlue() - ColorMetricHotSpotInterpreter.scalaColor[0].getBlue()) / (stepWidth + 1);

			for (int i = 1; i <= stepWidth; i++) {
				double b = ColorMetricHotSpotInterpreter.scalaColor[0].getBlue() + (bChange * i);
				double g = ColorMetricHotSpotInterpreter.scalaColor[0].getGreen() + (gChange * i);
				double r = ColorMetricHotSpotInterpreter.scalaColor[0].getRed() + (rChange * i);
				this.scale[i] = new Color(display, (int) r, (int) g, (int) b);
			}

			this.scale[(maxRange / 2)] = ColorMetricHotSpotInterpreter.scalaColor[1];

			stepWidth = (maxRange - ((maxRange / 2))) - 2;

			rChange = (ColorMetricHotSpotInterpreter.scalaColor[2].getRed() - ColorMetricHotSpotInterpreter.scalaColor[1].getRed()) / (stepWidth + 1);
			gChange = (ColorMetricHotSpotInterpreter.scalaColor[2].getGreen() - ColorMetricHotSpotInterpreter.scalaColor[1].getGreen()) / (stepWidth + 1);
			bChange = (ColorMetricHotSpotInterpreter.scalaColor[2].getBlue() - ColorMetricHotSpotInterpreter.scalaColor[1].getBlue()) / (stepWidth + 1);

			for (int i = 1; i <= stepWidth; i++) {
				double b = ColorMetricHotSpotInterpreter.scalaColor[1].getBlue() + (bChange * i);
				double g = ColorMetricHotSpotInterpreter.scalaColor[1].getGreen() + (gChange * i);
				double r = ColorMetricHotSpotInterpreter.scalaColor[1].getRed() + (rChange * i);
				this.scale[i + maxRange / 2] = new Color(display, (int) r, (int) g, (int) b);
			}

			this.scale[maxRange - 1] = ColorMetricHotSpotInterpreter.scalaColor[2];
		}
	}

	@Override
	public Color interpret(HotSpotResult result) {
		if (result.getMetricValue() >= maxRange)
			return scale[maxRange - 1];

		return scale[(int) result.getMetricValue()];
	}

}
