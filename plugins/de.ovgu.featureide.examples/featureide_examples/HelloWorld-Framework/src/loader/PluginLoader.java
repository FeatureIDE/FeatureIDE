package loader;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * Loads all plugins
 * 
 * @author Daniel Hohmann
 *
 */
public class PluginLoader {

	private static Map<Object, List<Object>> classInstanceMap = new HashMap<>();

	private static Map<String, List<String>> registerClasses() {
		Map<String, List<String>> map = new HashMap<>();
		try {
			Enumeration<URL> urls = ClassLoader.getSystemResources("info.xml");
			while (urls.hasMoreElements()) {
				URL url = urls.nextElement();
				DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
				DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
				Document doc = dBuilder.parse(url.openStream());

				/** Get all interfaces inside JAR **/
				NodeList nlInterfaces = doc.getElementsByTagName("interface");
				for (int i = 0; i < nlInterfaces.getLength(); i++) {
					Node interfaceNode = nlInterfaces.item(i);
					if (interfaceNode.getNodeType() == Node.ELEMENT_NODE) {
						String interfaceName = ((Element) interfaceNode).getAttribute("id");
						/** Get all implementing classes **/
						NodeList nlClasses = interfaceNode.getChildNodes();
						List<String> listClasses = new ArrayList<>();
						for (int j = 0; j < nlClasses.getLength(); j++) {
							Node classNode = nlClasses.item(j);
							if (classNode.getNodeType() == Node.ELEMENT_NODE) {
								Element e = (Element) classNode;
								listClasses.add(e.getTextContent());
							}
						}
						/** Update map at key **/
						if(map.containsKey(interfaceName) && !map.get(interfaceName).isEmpty()){
							map.get(interfaceName).addAll(listClasses);
						}
						else{
							map.put(interfaceName, listClasses);
						}
					}
				}
			}

		} catch (IOException e) {
			e.printStackTrace();
		} catch (ParserConfigurationException e) {
			e.printStackTrace();
		} catch (SAXException e) {
			e.printStackTrace();
		}
		return map;
	}

	static {
		/** Get information about all classes **/
		Map<String, List<String>> classes = registerClasses();
		for (String key : classes.keySet()) {
			List<Object> classInstanceList = new ArrayList<>();
			ClassLoader systemClassLoader = ClassLoader.getSystemClassLoader();
			for (String clWithInterface : classes.get(key)) {
				try {
					Class<?> loadClass = systemClassLoader.loadClass(clWithInterface);
					classInstanceList.add(loadClass.newInstance());
				} catch (InstantiationException | IllegalAccessException | ClassNotFoundException e) {
					e.printStackTrace();
				}
			}
			try {
				classInstanceMap.put(systemClassLoader.loadClass(key), classInstanceList);
			} catch (ClassNotFoundException e) {
				e.printStackTrace();
			}
		}

	}

	/**
	 * Loads classes implementing the given interface
	 * 
	 * @param cl
	 *            Class implementing the interface <b>T</b>
	 * @return List
	 */
	public static <T> List<T> load(Class<T> cl) {
		final List <T> list = new ArrayList<>();
		for(Object clKey : classInstanceMap.keySet()){
			if(cl.equals(clKey)){
				for(Object obj : classInstanceMap.get(cl)){
					list.add(cl.cast(obj));
				}
			}
		}
		return list;
	}
}
