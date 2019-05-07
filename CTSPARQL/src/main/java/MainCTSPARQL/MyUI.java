package MainCTSPARQL;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Scanner;
import java.util.Set;

import javax.servlet.annotation.WebServlet;

import org.apache.log4j.varia.NullAppender;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.vaadin.aceeditor.AceEditor;
import org.vaadin.aceeditor.AceMode;
import org.vaadin.aceeditor.AceTheme;

import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.sparql.core.Var;
import com.vaadin.annotations.Theme;
import com.vaadin.annotations.VaadinServletConfiguration;
import com.vaadin.icons.VaadinIcons;
import com.vaadin.server.ThemeResource;
import com.vaadin.server.VaadinRequest;
import com.vaadin.server.VaadinServlet;
import com.vaadin.ui.Button;
import com.vaadin.ui.Button.ClickEvent;
import com.vaadin.ui.ComboBox;
import com.vaadin.ui.HorizontalLayout;
import com.vaadin.ui.Image;
import com.vaadin.ui.Notification;
import com.vaadin.ui.Panel;
import com.vaadin.ui.TextArea;
import com.vaadin.ui.TextField;
import com.vaadin.ui.UI;
import com.vaadin.ui.VerticalLayout;
import com.vaadin.ui.themes.ValoTheme;

import CTSPARQL.TSPARQL;

import com.vaadin.server.ErrorEvent;
import com.vaadin.server.ErrorHandler;

/**
 * This UI is the application entry point. A UI may either represent a browser
 * window (or tab) or some part of an HTML page where a Vaadin application is
 * embedded.
 * <p>
 * The UI is initialized using {@link #init(VaadinRequest)}. This method is
 * intended to be overridden to add component to the user interface and
 * initialize non-component functionality.
 */
@Theme("mytheme")
public class MyUI extends UI {

	OWLOntologyManager manager = null;
	OWLOntologyManager manager_rdf = null;
	OWLOntologyManager manager_owl = null;
	OWLOntology ontology = null;
	OWLOntology ont_rdf = null;
	OWLOntology ont_owl = null;
	OWLDataFactory dataFactory = null;
	OWLDataFactory df_rdf = null;
	OWLDataFactory df_owl = null;
	String rdf = "C:/rdf-vocabulary.owl";
	String owl = "C:/owl-vocabulary.owl";
	OWLReasoner reasoner;	
	ComboBox<String> cb_type_validity = new ComboBox<String>();
	ComboBox<Var> cb_vars = new ComboBox<Var>(); 
	public static String readStringFromURL(String requestURL) throws IOException {
		try (Scanner scanner = new Scanner(new URL(requestURL).openStream(), StandardCharsets.UTF_8.toString())) {
			scanner.useDelimiter("\\A");
			return scanner.hasNext() ? scanner.next() : "";
		}
	}

	@Override
	protected void init(VaadinRequest vaadinRequest) {
	
		final VerticalLayout layout = new VerticalLayout();		 
		Image lab = new Image(null, new ThemeResource("banner-tsparql.jpg"));
		lab.setWidth("100%");
		lab.setHeight("200px");
		TextField filet = new TextField();
		filet.setStyleName("multi-line-caption");
		filet.setSizeFull();
		filet.setValue("social-network-2019.owl");

		/*setErrorHandler(new ErrorHandler() {
            
            @Override
            public void error(com.vaadin.server.ErrorEvent event) {
                //System.out.println(event.getThrowable().getMessage());
                Notification.show(event.getThrowable().getMessage());
                restore("C:/"+filet.getValue());
            }
            
        });*/

		HorizontalLayout hlb = new HorizontalLayout();
		Button correctness = new Button("Correctness");
		correctness.setStyleName(ValoTheme.BUTTON_FRIENDLY);
		correctness.setIcon(VaadinIcons.AMBULANCE);
		//Button checking = new Button("Consistency Checking");
		//checking.setStyleName(ValoTheme.BUTTON_DANGER);
		//checking.setIcon(VaadinIcons.CHECK);   
		Button type_validity = new Button("Type Validity");
		type_validity.setStyleName(ValoTheme.BUTTON_PRIMARY);
		type_validity.setIcon(VaadinIcons.HEART);
		Button run_type_validity = new Button("Run Type Validity");
		run_type_validity.setStyleName(ValoTheme.BUTTON_FRIENDLY);
		run_type_validity.setIcon(VaadinIcons.PLAY);	
		HorizontalLayout hlt = new HorizontalLayout();
		hlb.addComponent(correctness);
		//hlb.addComponent(checking);
		hlb.addComponent(type_validity);
		hlt.addComponent(cb_type_validity);
		hlt.addComponent(cb_vars);
		hlt.addComponent(run_type_validity);
		cb_type_validity.setVisible(false);
		cb_type_validity.setWidth("600px");
		cb_vars.setVisible(false);
		cb_type_validity.setEmptySelectionAllowed(false);
		cb_vars.setEmptySelectionAllowed(false);	
		run_type_validity.setVisible(false);		
		Panel edS = new Panel();
		Panel resP = new Panel();
		edS.setSizeFull();
		resP.setSizeFull();
		AceEditor editor = new AceEditor();
		editor.setHeight("300px");
		editor.setWidth("100%");
		editor.setFontSize("12pt");
		editor.setMode(AceMode.sql);
		editor.setTheme(AceTheme.eclipse);
		editor.setUseWorker(true);
		editor.setReadOnly(false);
		editor.setShowInvisibles(false);
		editor.setShowGutter(false);
		editor.setShowPrintMargin(false);
		editor.setUseSoftTabs(false);
		
		String type1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { sn:foo sn:attends_to sn:Event }\n";
		
		 
		String type2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:attends_to ?EVENT . ?USER sn:friend_of ?EVENT}\n";
		 
		String type3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER sn:age ?AGE . ?EVENT sn:age ?USER}\n";
		 
		String type4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER sn:name ?EVENT . ?EVENT rdf:type sn:Event}\n";
		 
		String type5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER sn:name ?NAME . ?USER sn:age ?NAME}\n";
		
		String type6 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER sn:friend_of ?USER }\n";

		 
		String type7 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER rdf:type sn:User . ?USER rdf:type sn:Event }\n";

		 
		String type8 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER rdf:type sn:User . \n"
				+ "?USER rdf:type ?TYPE .\n"
				+ "?TYPE rdfs:subClassOf sn:Event }\n";
   
		String type9 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?Value WHERE { ?USER sn:name ?VALUE .\n"
				+ "FILTER (?VALUE > 10) }\n";
	 
		String type10 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER rdf:type 10 }\n";
			
		String val1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER1 ?USER2 ?AU1 ?AU2 WHERE {\n" 
				+ "?USER1 sn:age ?AU1 . ?USER2 sn:age ?AU2 . \n"
				+ "FILTER(?AU1-?AU2 < 10) .\n" 
				+ "FILTER(?AU1 > 40 ).\n" 
				+ "FILTER (?AU2 < 18) }\n";

		String val2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AU WHERE {\n" 
				+ "?USER sn:age ?AU . " 
				+ "FILTER(?AU > 30 ).\n" 
				+ "FILTER (?AU < 31) }\n";

		String val3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?HU WHERE {\n" 
				+ "?USER sn:height ?HU  . " 
				+ "FILTER(?HU > 130 ).\n"
				+ "FILTER (?HU < 131) }\n";

		String val4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE WHERE {\n" 
				+ "?USER sn:age ?AGE .\n" 
				+ "FILTER (?AGE > 50) .\n"
				+ "FILTER EXISTS {SELECT ?USER2 WHERE {\n" 
				+ "?USER2 sn:age ?AGE2 .\n" 
				+ "FILTER (?AGE2 < 25) .\n"
				+ "FILTER (?AGE < ?AGE2 ) }\n" 
				+ "}}\n";

		String val5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE WHERE {\n" 
				+ "?USER rdf:type sn:Young .\n" 
				+ "?USER sn:age ?AGE .\n"
				+ "FILTER (?AGE > 50) " + "}\n";

		String val6 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE WHERE {\n" 
				+ "?USER sn:age ?AGE .\n" 
				+ "FILTER (?AGE > 50) .\n"
				+ "MINUS {SELECT ?USER2 WHERE {\n" 
				+ "?USER2 sn:age ?AGE2 .\n" 
				+ "FILTER (?AGE2 < 25) .\n"
				+ "FILTER (?AGE < ?AGE2 ) }\n" 
				+ "}}\n";

		String val7 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE WHERE {\n" 
				+ "?USER sn:age ?AGE .\n" 
				+ "FILTER (?AGE > 50) .\n"
				+ "OPTIONAL {SELECT ?USER2 WHERE {\n" 
				+ "?USER2 sn:age ?AGE2 .\n" 
				+ "FILTER (?AGE2 < 25) .\n"
				+ "FILTER (?AGE < ?AGE2 ) }\n" 
				+ "}}\n";

		String val8 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE {\n" 
				+ "?USER sn:age ?AGE . \n"
				+ "FILTER (?AGE > 50) .\n"
				+ "{SELECT ?USER2 WHERE {\n" 
				+ "?USER2 sn:age ?AGE2 .\n" 
				+ "?USER2 rdf:type sn:Young .\n"
				+ "FILTER (?AGE < ?AGE2 ) }\n" 
				+ "}}\n";

		String val9 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?NAME WHERE {\n" 
				+ "?USER sn:name ?name .\n"
				+ "FILTER ('jesus' < ?NAME) .\n"
				+ "FILTER (?NAME < 'antonio') }\n";

		String val10 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?EVENT ?DATE WHERE {\n" 
				+ "?EVENT sn:date ?date .\n"
				+ "FILTER ('2017-09-04T01:00:00Z' < ?DATE) ."
				+ "FILTER (?DATE < '2017-09-03T02:00:00Z') }\n";

		
		String test1 = 
				"# ?USER1 rdf:type sn:Influencer\n"
				+"# Influencer: User having at least once more than 100 todayfollowers\n"
				+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER1 ?USER2 ?TF1 ?TF2 WHERE {\n"  
				+ "?USER1 sn:todayfollowers ?TF1 .\n"
				+ "?USER2 sn:todayfollowers ?TF2 .\n "
				+ "FILTER(?TF2-?TF1 < 300) .\n"
				+ "FILTER(?TF1 > 50 ).\n"
				+ "FILTER (?TF2 > 100) }\n";
		
		String test2 = 
				"# ?USER1 rdf:type sn:Influencer\n"
						+"# Influencer: User having at least once more than 100 todayfollowers\n"
						+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER1 ?USER2 ?TF1 ?TF2 WHERE {\n"  
						+ "?USER1 sn:todayfollowers ?TF1 .\n"
						+ "?USER2 sn:todayfollowers ?TF2 .\n "
						+ "FILTER(?TF2-?TF1 < 300) .\n"
						+ "FILTER(?TF2 > 100 )}\n";
		
		String test3 = 
				"# ?USER rdf:type sn:Influencer\n"
						+"#Influencer: User having at least once more than 100 todayfollowers\n"
						+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER ?TF WHERE {\n"  
						+ "?USER sn:todayfollowers ?TF .\n "
						+ "FILTER(?TF < 300)}\n";
		
	
		String test4 = 
				"# ?USER rdf:type sn:Influencer\n"
						+"# Influencer: User having at least once more than 100 todayfollowers\n"
						+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER ?TF WHERE {\n"  
						+ "?USER sn:todayfollowers ?TF .\n "
						+ "FILTER(?TF > 50)}\n";
		 
		String test5 = 
				"# ?USER rdf:type sn:Influencer\n"
						+"# Influencer: User having at least once more than 100 todayfollowers\n"
						+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n"  
						+ "?USER rdf:type sn:User .\n"
						+ "?USER sn:age 40}";
						
			
		String test6 = 
				"# ?USER rdf:type sn:Verified\n"
				+"# Verified: User having verified set to 1\n"
						+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n"  
						+ "?USER sn:verified 1}";
		 
		String test7 = 
				"# ?USER rdf:type sn:Verified\n"
						+"# Verified: User having verified set to 1\n"
						+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
						+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER ?V WHERE {\n"  
						+ "?USER sn:verified ?V.\n"
						+ "FILTER(?V>1)}";
			
		
		
		String test8 = 
				"# ?MESSAGE rdf:type sn:Shared\n"
				+"# Shared: Message shared by at least one user\n"
				+"# Bug: ?MESSAGE sn:shared_by ?USER2 should be added to the query\n"
				+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" 
				+ "?USER sn:age ?AGE .\n"
				+ "FILTER(?AGE >40) .\n"
				+ "{SELECT ?USER ?MESSAGE WHERE {\n" 
				+ "?MESSAGE sn:sent_by ?USER  }}}\n";
		 
		 
		
		String test9 = 
				"# ?MESSAGE rdf:type sn:Shared\n"
				+"# Shared: Message shared by at least one user\n"
				+"# Bug: ?MESSAGE sn:shared_by ?USER2 and ?USER sn:sent_by ?MESSAGE should be added to the query\n"
				+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" 
				+ "?USER sn:age ?AGE .\n"
				+ "FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER ?MESSAGE WHERE {\n"
				+ "?MESSAGE sn:liked_by ?USER2 }}}\n";
		 
		 
		String test10 = 
				"# ?USER rdf:type Leader\n"
				+"# Leader: User who send a message shared by some other user\n"
				+ "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" 
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" 
				+ "?USER sn:age ?AGE .\n"
				+ "FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER ?MESSAGE WHERE {\n" 
				+ "?MESSAGE sn:sent_by ?USER .\n"
				+ "?MESSAGE sn:shared_by ?USER2 }}}\n";
			
		 
		ComboBox<String> examplest = new ComboBox<>("Examples of Typing");
		examplest.setEmptySelectionAllowed(false);
		examplest.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6", "Example 7",
				"Example 8", "Example 9", "Example 10");
		
		/*ComboBox<String> examplesc = new ComboBox<>("Examples of Consistency Checking");
		examplesc.setEmptySelectionAllowed(false);
		examplesc.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6", "Example 7",
				"Example 8", "Example 9", "Example 10");*/
		
		ComboBox<String> examplestst = new ComboBox<>("Examples of Type Validity");
		examplestst.setEmptySelectionAllowed(false);
		examplestst.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6", "Example 7",
				"Example 8", "Example 9", "Example 10");

		examplest.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				Notification.show("No example selected");
			} else {
				if (event.getValue() == "Example 1") {					 
					editor.setValue(type1);
				} else if (event.getValue() == "Example 2") {					 
					editor.setValue(type2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(type3);
				} else if (event.getValue() == "Example 4") {
 					editor.setValue(type4);
				} else if (event.getValue() == "Example 5") {					 
					editor.setValue(type5);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(type6);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(type7);
				} else if (event.getValue() == "Example 8") {
 					editor.setValue(type8);
				} else if (event.getValue() == "Example 9") {
					editor.setValue(type9);
				} else if (event.getValue() == "Example 10") {				 
					editor.setValue(type10);
				}
				 
				
			}
		});
		
		/*examplesc.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				Notification.show("No example selected");
			} else {
				if (event.getValue() == "Example 1") {				 
					editor.setValue(val1);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(val2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(val3);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(val4);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(val5);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(val6);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(val7);
				} else if (event.getValue() == "Example 8") {
					editor.setValue(val8);
				} else if (event.getValue() == "Example 9") {
					editor.setValue(val9);
				} else if (event.getValue() == "Example 10") {
					editor.setValue(val10);
				}  
			}
		});*/
		
		examplestst.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				Notification.show("No example selected");
			} else {
				if (event.getValue() == "Example 1") {
 					editor.setValue(test1);
				} else if (event.getValue() == "Example 2") {
 					editor.setValue(test2);
				} else if (event.getValue() == "Example 3") {
 					editor.setValue(test3);
				} else if (event.getValue() == "Example 4") {			 
					editor.setValue(test4);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(test5);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(test6);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(test7);
				} else if (event.getValue() == "Example 8") {
 					editor.setValue(test8);
				} else if (event.getValue() == "Example 9") {
 					editor.setValue(test9);
				} else if (event.getValue() == "Example 10") {
 					editor.setValue(test10);
				}  
			}
		});

		editor.setValue(type1);
		editor.setDescription("SPARQL Query");
		TextArea result = new TextArea();
		result.setHeight("300px");
		result.setWidth("100%");
		result.setStyleName("multi-line-caption");
		AceEditor editorOntology = new AceEditor();
		Panel edO = new Panel();
		edO.setSizeFull();

		correctness.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {	
				result.setValue("");
				manager = OWLManager.createOWLOntologyManager();		
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/"+filet.getValue());
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {

					e2.printStackTrace();
				}
				manager_owl = OWLManager.createOWLOntologyManager();
				df_owl = manager_owl.getOWLDataFactory();
				ont_owl = null;
				File file_owl = new File(owl);
				try {
					ont_owl = manager_owl.loadOntologyFromOntologyDocument(file_owl);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}

				manager_rdf = OWLManager.createOWLOntologyManager();
				df_rdf = manager_rdf.getOWLDataFactory();
				ont_rdf = null;
				File file_rdf = new File(rdf);
				try {
					ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}
				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				PrintStream old = System.out;
				System.setOut(ps);
				TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
						df_rdf, df_owl,"C:/"+filet.getValue());
				t.SPARQL_CORRECTNESS(editor.getValue());
				System.out.flush();
				System.setOut(old);
				result.setValue(baos.toString());
				System.out.println(baos.toString());
			}
		});
		/*checking.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {
				result.setValue("");
				manager = OWLManager.createOWLOntologyManager();
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/"+filet.getValue());
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}
				manager_owl = OWLManager.createOWLOntologyManager();
				df_owl = manager_owl.getOWLDataFactory();
				ont_owl = null;
				File file_owl = new File(owl);
				try {
					ont_owl = manager_owl.loadOntologyFromOntologyDocument(file_owl);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}
				manager_rdf = OWLManager.createOWLOntologyManager();
				df_rdf = manager_rdf.getOWLDataFactory();
				ont_rdf = null;
				File file_rdf = new File(rdf);
				try {
					ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}
				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				PrintStream old = System.out;
				System.setOut(ps);
				TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
						df_rdf, df_owl,"C:/"+filet.getValue());
				t.SPARQL_CHECKING(editor.getValue());
				System.out.flush();
				System.setOut(old);
				result.setValue(baos.toString());
			}
		});*/
		type_validity.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {		
				result.setValue("");
				manager = OWLManager.createOWLOntologyManager();
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/"+filet.getValue());
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}		
				cb_type_validity.clear();
				cb_vars.clear();			
				cb_type_validity.setVisible(true);
				cb_vars.setVisible(true);
				run_type_validity.setVisible(true);			
				Set<OWLClass> classes_testing = ontology.getClassesInSignature();
				List<String> names = new ArrayList<String>();
				String urio = ontology.getOntologyID().getOntologyIRI().toString();
				for (OWLClass c:classes_testing)
				{
				if (c.getIRI().getStart().equals(urio+"#")) {names.add(c.getIRI().toString());}
				}
				cb_type_validity.setItems(names);				
				com.hp.hpl.jena.query.Query query = QueryFactory.create(editor.getValue());
				List<Var> vars = query.getProjectVars();
				cb_vars.setItems(vars);
				type_validity.setEnabled(false);
				correctness.setEnabled(false);
				//checking.setEnabled(false);
			}
		});
		
		run_type_validity.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {		
				if (cb_type_validity.isEmpty() || cb_vars.isEmpty())
				{Notification.show("Please select a class and an individual");
				}
				else
				{
				manager_owl = OWLManager.createOWLOntologyManager();
				df_owl = manager_owl.getOWLDataFactory();
				ont_owl = null;
				File file_owl = new File(owl);
				try {
					ont_owl = manager_owl.loadOntologyFromOntologyDocument(file_owl);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}
				manager_rdf = OWLManager.createOWLOntologyManager();
				df_rdf = manager_rdf.getOWLDataFactory();
				ont_rdf = null;
				File file_rdf = new File(rdf);
				try {
					ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
				} catch (OWLOntologyCreationException e2) {
					e2.printStackTrace();
				}
				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				PrintStream old = System.out;
				System.setOut(ps);	 
				TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
						df_rdf, df_owl,"C:/"+filet.getValue());
				Optional<Var> variable_testing = cb_vars.getSelectedItem();
				Optional<String> type_testing = cb_type_validity.getSelectedItem();
				String var_name = variable_testing.get().getName().replace('?', ' ').replaceAll("\\s", "");  
				String type_name = type_testing.get();						
				t.SPARQL_TYPE_VALIDITY(editor.getValue(),var_name,type_name);		
				cb_type_validity.setVisible(false);
				cb_vars.setVisible(false);
				run_type_validity.setVisible(false);	
				type_validity.setEnabled(true);
				//checking.setEnabled(true);
				correctness.setEnabled(true);
				System.out.flush();
				System.setOut(old);
				result.setValue(baos.toString());
			}
			}
		});
		edS.setContent(editor);
		resP.setContent(result);
		HorizontalLayout examplesall = new HorizontalLayout();
		layout.addComponent(lab);
		examplesall.addComponent(examplest);
		//examplesall.addComponent(examplesc);
		examplesall.addComponent(examplestst);
		layout.addComponent(examplesall);
		layout.addComponent(filet);
		layout.addComponent(edS);
		layout.addComponent(hlb);
		layout.addComponent(hlt);
		layout.addComponent(resP);
		String ontology;
		try {
			ontology = readStringFromURL("file:///C:/" + filet.getValue());
			editorOntology.setValue(ontology);
		} catch (IOException e) {
			Notification.show(e.getMessage());
		}
		edO.setContent(editorOntology);
		editorOntology.setHeight("300px");
		editorOntology.setWidth("100%");
		editorOntology.setFontSize("12pt");
		editorOntology.setMode(AceMode.sql);
		editorOntology.setTheme(AceTheme.eclipse);
		editorOntology.setUseWorker(true);
		editorOntology.setReadOnly(false);
		editorOntology.setShowInvisibles(false);
		editorOntology.setShowGutter(false);
		editorOntology.setShowPrintMargin(false);
		editorOntology.setUseSoftTabs(false);
		layout.addComponent(edO);
		setContent(layout);
		this.setSizeFull();
	}
	
	public void restore(String file) {
		FileInputStream source2 = null;
		FileOutputStream dest2 = null;
		try {
			source2 = new FileInputStream("tmp.owl");
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		try {
			dest2 = new FileOutputStream(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		byte[] buffer2 = new byte[1024];
		int length2;
		try {
			while ((length2 = source2.read(buffer2)) > 0) {
				dest2.write(buffer2, 0, length2);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

	};
	@WebServlet(urlPatterns = "/*", name = "MyUIServlet", asyncSupported = true)
	@VaadinServletConfiguration(ui = MyUI.class, productionMode = false)
	public static class MyUIServlet extends VaadinServlet {
	}
}
