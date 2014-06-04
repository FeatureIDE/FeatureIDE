
//import the packages for using the classes in them into this class
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/**
 *A class for creating JFontDialog
 */
public class Fonts extends JDialog {
	//Constructor of Fonts
	public Fonts(final Notepad n){
		//for setting the title
		setTitle("Font Dialog");
		setResizable(false);
		/**
		 *setting the layout (GridLayout: 5 rows & 2 columns)
		 *add font JLabel, add font JComboBox
		 *add type JLabel, add type JComboBox
		 *add size JLabel, add size JComboBox
		 *add preview JLabel,add test JLabel
		 *add ok button, add cancel button
		 */
		JPanel jp = new JPanel();
		jp.setLayout(new GridLayout(5,2,1,1));
		JLabel fjl = new JLabel("Fonts: ");
		jp.add(fjl);
		String fonts[]=GraphicsEnvironment.getLocalGraphicsEnvironment().getAvailableFontFamilyNames();
		final JComboBox fjcb = new JComboBox(fonts);
		jp.add(fjcb);
		JLabel sjl = new JLabel("Sizes: ");
		jp.add(sjl);
		String sizes[] = {"8","10","12","14","16","18","20","24","28","32","48","72"};
		final JComboBox sjcb = new JComboBox(sizes);
		jp.add(sjcb);
		final JLabel tjl = new JLabel("Types: ");
		jp.add(tjl);
		String types[] = {"Regular", "Bold", "Italic", "Bold Italic"};
		final JComboBox tjcb = new JComboBox(types);
		jp.add(tjcb);
		JLabel jjl = new JLabel("Preview:");
		jp.add(jjl);
		final JLabel jl = new JLabel("AaBaCcDdeEfFgGhHjJ");
		jl.setBorder(BorderFactory.createEtchedBorder());
		jp.add(jl);
		JButton okjb = new JButton("OK");
		JButton cajb = new JButton("Cancel");
		jp.add(okjb);
		jp.add(cajb);
		//add JPanel to the Container
		this.getContentPane().add(jp);
		//Centering the window
		Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
		setLocation((screenSize.width-getWidth())/2,(screenSize.height-getHeight())/2);
		//add action listener to Font JComboBox to get the selected item for setting the preview
		fjcb.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				jl.setFont(new Font(String.valueOf(fjcb.getSelectedItem()),tjcb.getSelectedIndex(),14));
			}
		});
		//add action listener to Type JComboBox to get the selected index for setting the preview
		tjcb.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				jl.setFont(new Font(String.valueOf(fjcb.getSelectedItem()),tjcb.getSelectedIndex(),14));
			}
		});
		//making an action for ok button, so we can change the font
		okjb.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				Font font = new Font(String.valueOf(fjcb.getSelectedItem()), tjcb.getSelectedIndex(),
					Integer.parseInt(String.valueOf(sjcb.getSelectedItem())));
				n.getTextArea().setFont(font);
				//after we chose the font, then the JDialog will be closed
				setVisible(false);
			}
		});	
		//making an action for cancel button, so we can return to the old font.
		cajb.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				//after we cancel the, then the JDialog will be closed
				setVisible(false);
			}
		});
	}
}
