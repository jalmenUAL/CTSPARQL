package sparql.tsparql.WSPARQL;

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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import javax.servlet.annotation.WebServlet;

import org.apache.log4j.varia.NullAppender;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.vaadin.aceeditor.AceEditor;
import org.vaadin.aceeditor.AceMode;
import org.vaadin.aceeditor.AceTheme;

import com.clarkparsia.owlapi.explanation.GlassBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import com.hp.hpl.jena.sparql.core.TriplePath;
import com.vaadin.annotations.Push;
import com.vaadin.annotations.Theme;
import com.vaadin.annotations.VaadinServletConfiguration;
import com.vaadin.server.VaadinRequest;
import com.vaadin.server.VaadinServlet;
import com.vaadin.ui.Button;
import com.vaadin.ui.Button.ClickEvent;
import com.vaadin.ui.ComboBox;
import com.vaadin.ui.HorizontalLayout;
import com.vaadin.ui.Label;
import com.vaadin.ui.Notification;
import com.vaadin.ui.Panel;
import com.vaadin.ui.TextField;
import com.vaadin.ui.UI;
import com.vaadin.ui.VerticalLayout;
import com.vaadin.ui.themes.ValoTheme;

import testingSPARQL.TSPARQL2;



/**
 * This UI is the application entry point. A UI may either represent a browser window 
 * (or tab) or some part of an HTML page where a Vaadin application is embedded.
 * <p>
 * The UI is initialized using {@link #init(VaadinRequest)}. This method is intended to be 
 * overridden to add component to the user interface and initialize non-component functionality.
 */
@Theme("mytheme")
public class MyUI2 extends UI {
	
	
	
	OWLOntologyManager manager = null;
	OWLOntologyManager manager_rdf = null;
	OWLOntologyManager manager_owl = null;
	OWLOntology ontology = null;
	OWLOntology ont_rdf = null;
	OWLOntology ont_owl = null;
	OWLDataFactory dataFactory = null;
	OWLDataFactory df_rdf = null;
	OWLDataFactory df_owl = null;
	String rdf="rdf-vocabulary.owl";
	String owl="owl-vocabulary.owl";
	String file="social-network-2018.owl";
	PelletReasonerFactory pfactory;
	Configuration configuration;
	OWLReasoner reasoner;
	HSTExplanationGenerator multExplanator;
	GlassBoxExplanation exp;

	public static String readStringFromURL(String requestURL) throws IOException {
		try (Scanner scanner = new Scanner(new URL(requestURL).openStream(), StandardCharsets.UTF_8.toString())) {
			scanner.useDelimiter("\\A");
			return scanner.hasNext() ? scanner.next() : "";
		}
	}

	
	
	@Override
	protected void init(VaadinRequest vaadinRequest) {
		
		
		
		
		manager = OWLManager.createOWLOntologyManager();
		dataFactory = manager.getOWLDataFactory();
		ontology = null;
		
		File fileName = new File(file);

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

		//pfactory = new PelletReasonerFactory();
		//configuration = new Configuration();
		//configuration.throwInconsistentOntologyException = false;
		//reasoner = pfactory.createReasoner(ontology, configuration);
		 
		
		final VerticalLayout layout = new VerticalLayout();

		Label lab = new Label("TSPARQL: Typing, Consistency Checking and Testing of SPARQL");
		//lab.addStyleName(ValoTheme.LABEL_H1);
		lab.addStyleName(ValoTheme.LABEL_COLORED);

		TextField filet = new TextField();
		filet.setSizeFull();
		filet.setValue("social-network-2018.owl");

		HorizontalLayout hlb = new HorizontalLayout();
		Button typing = new Button("Typing");
		Button checking = new Button("Consistency Checking");
		Button testing = new Button("Testing");
		hlb.addComponent(typing);
		hlb.addComponent(checking);
		hlb.addComponent(testing);

		Panel edS = new Panel();
		Panel resP = new Panel();
		edS.setSizeFull();
		resP.setSizeFull();

		AceEditor editor = new AceEditor();
		editor.setHeight("300px");
		editor.setWidth("2000px");
		editor.setFontSize("12pt");
		editor.setMode(AceMode.sql);
		editor.setTheme(AceTheme.eclipse);
		editor.setUseWorker(true);
		editor.setReadOnly(false);
		editor.setShowInvisibles(false);
		editor.setShowGutter(false);
		editor.setShowPrintMargin(false);
		editor.setUseSoftTabs(false);

		// Wrong type 0
				String type0 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { sn:foo sn:attends_to sn:Event }\n";
				// Wrong type 1
				String type1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:name ?EVENT . ?EVENT sn:name ?NAME}\n";
				// Wrong type 2
				String type2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:name ?EVENT . ?EVENT rdf:type sn:Event}\n";
				// Wrong type 3
				String type3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:name ?EVENT . ?EVENT rdf:type ?TYPE}\n";
				// Wrong type 4
				String type4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:name ?NAME . ?USER sn:age ?NAME}\n";
				// Wrong type 5
				String type5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:attends_to ?EVENT . ?USER sn:friend_of ?EVENT}\n";

				// Wrong type 6
				String type6 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:attends_to ?EVENT . ?EVENT sn:friend_of ?USER}\n";

				// Wrong type 7
				String type7 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:attends_to ?USER }\n";

				// Wrong type 8
				String type8 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:friend_of ?USER }\n";

				// Wrong type 9
				String type9 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER rdf:type sn:User . ?USER rdf:type sn:Event }\n";

				// Wrong type 10
				String type10 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER rdf:type sn:User . ?USER rdf:type ?type "
						+ ". ?type rdfs:subClassOf sn:Event }\n";

				// Wrong type 11 --correcta
				String type11 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER ?Prop sn:user . ?Prop rdf:type sn:event  }\n";

				// Wrong type 12 --correcta
				String type12 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER ?Prop sn:user . ?USER rdf:type ?Prop  }\n";

				// Wrong type 13
				String type13 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER ?Prop ?Value . ?USER sn:name ?Prop }\n";

				// Wrong type 14 -- TO DO
				String type14 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER sn:name ?Value . FILTER (?Value > 10) }\n";

				// Wrong type 15
				String type15 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE { ?USER rdf:type 10 }\n";

				String val0 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE != 50) "
						+ ". BIND ((?AGE+?AGE) AS ?U) }";

				String val1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER1 ?USER2 WHERE {\n" + "?USER1 sn:age ?AU1 . ?USER2 sn:age ?AU2 . \n "
						+ "FILTER(?AU1-?AU2 < 10) .\n" + "FILTER(?AU1 > 40 ).\n" + "FILTER (?AU2 < 18) }\n";

				String val2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AU . " + "FILTER(?AU > 30 ).\n" + "FILTER (?AU < 31) }\n";

				String val3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:height ?HU  . " + "FILTER(?HU > 130 ).\n"
						+ "FILTER (?HU < 131) }\n";

				String val4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n"
						+ "FILTER EXISTS {SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "FILTER (?AGE2 < 25) .\n"
						+ "FILTER (?AGE < ?AGE2 ) }\n" + "}}\n";

				String val5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:height ?H .\n" + "FILTER (?H > 175) .\n"
						+ "FILTER EXISTS {SELECT ?USER2 WHERE {\n" + "?USER2 sn:height ?H2 .\n" + "FILTER (?H2 < 176) .\n"
						+ "FILTER (?H < ?H2 ) }\n" + "}}\n";

				String val6 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER ?USER2 WHERE {\n" + "?USER rdf:type sn:Young .\n" + "?USER sn:age ?AGE .\n"
						+ "FILTER (?AGE > 50) .\n" + "?USER sn:attends_to ?Event" + "}\n";

				String val7 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER rdf:type sn:Young .\n" + "?USER sn:age ?AGE .\n"
						+ "FILTER (?AGE > 50) .\n" + "}\n";

				String val8 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n"
						+ "OPTIONAL {SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "FILTER (?AGE2 < 25) .\n"
						+ "FILTER (?AGE < ?AGE2 ) }\n" + "}}\n";

				String val9 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n"
						+ "{SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "FILTER (?AGE2 < 25) .\n"
						+ "FILTER (?AGE < ?AGE2 ) }\n" + "}}\n";

				String val10 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n"
						+ "{SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "?USER2 rdf:type sn:Young .\n"
						+ "FILTER (?AGE < ?AGE2 ) }\n" + "}}\n";

				String val11 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n"
						+ "OPTIONAL {SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "FILTER (?AGE2 < 25) .\n"
						+ "FILTER (?AGE < ?AGE2 ) . ?USER2 rdf:type sn:Young  }\n" + "}}\n";

				String val12 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n"
						+ "MINUS {SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "FILTER (?AGE2 < 25) .\n"
						+ "FILTER (?AGE < ?AGE2 ) . ?USER2 rdf:type sn:Young  }\n" + "}}\n";

				String val13 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER rdf:type ?Type . ?Type rdfs:subClassOf sn:Young .\n"
						+ "?USER sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n" + "}\n";
				
				String val14 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:name ?name . FILTER ('z' < ?name) . FILTER (?name < 'a') }\n";
				
				String val14b = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?EVENT WHERE {\n" + "?EVENT sn:date ?date . FILTER ('2017-09-04T01:00:00Z' < ?date) "
								+ ". FILTER (?date < '2017-09-04T02:00:00Z') }\n";

				String val15 = // SOLO A NIVEL DE RESTRICCION, NO DE INSTANCIA
						"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
								+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n"
								+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
								+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
								+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
								+ "SELECT ?AGE WHERE {\n" + "sn:antonio sn:age ?AGE .\n" + "FILTER (?AGE > 50) .\n" + "}\n";

				String val16 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?USER WHERE {\n" + "?USER sn:added_by ?USER2 . ?USER sn:friend_of sn:antonio\n" + "}\n";

				String val17 = 
						"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
								+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n"
								+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
								+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
								+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
								+ "SELECT ?CARD WHERE {\n" + "?PROP owl:minCardinality ?CARD . \n" + " FILTER(?CARD = -1)}\n";

				String test1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?user1 ?event ?user2 WHERE {\r\n" + "?event sn:added_by ?user1 . ?user1 sn:age ?age1 . "
						+ "?user1 sn:friend_of ?user2 . ?user2 sn:age ?age2 .\r\n" + "FILTER (?age1 >= 40) . "
						+ "?user2 rdf:type sn:Mature \r\n" // TESTING
						+ "} ";

				String test2 = // SOLO A NIVEL DE RESTRICCION, NO DE INSTANCIA
						"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
								+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n"
								+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
								+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
								+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
								+ "SELECT ?user ?name1 ?name2 WHERE {\r\n" + "?user sn:name ?name1 ;  sn:age ?age1 .\r\n"
								+ "sn:antonio sn:name ?name2 ; sn:age ?age2 .\r\n" + "FILTER (?age1 > ?age2 ) ."
								+ " ?user rdf:type sn:Young " // TESTING
								+ "} ";

				String test3 = // NO SE PERMITEN AGREGADORES
						"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
								+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n"
								+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
								+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
								+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
								+ "SELECT ?event ?likes ?attendees WHERE { " + "?event sn:created_by ?user\r\n" + "{\r\n"
								+ "SELECT ?event (COUNT(?person) AS ?likes)\r\n"
								+ "WHERE { ?person sn:likes ?event . ?person sn:age ?age . FILTER(?age > 40) } GROUP BY ?event\r\n"
								+ "}UNION\r\n" + "{\r\n" + "SELECT ?event (COUNT(?person) AS ?attendees)\r\n"
								+ "WHERE { ?person sn:attends_to ?event . ?person sn:age ?age . FILTER(?age > 40) }\r\n"
								+ "GROUP BY ?event } .\r\n" + "FILTER (?likes > 10) . FILTER (?attendees > 20) . " + "} ";

				String test4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?user ?event  WHERE {\r\n" + "?event sn:added_by ?user . " + "?user sn:likes ?event ."
						+ "?event rdf:type sn:Non_popular \r\n" // TESTING
						+ "} ";

				String test5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
						+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
						+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
						+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
						+ "SELECT ?user ?event  WHERE {\r\n" + "?event sn:added_by ?user . " + "?user sn:attends_to ?event ."
						+ "?event rdf:type sn:Non_popular \r\n" // TESTING
						+ "} ";

		ComboBox<String> examples = new ComboBox<>("Select an Example");
		examples.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6","Example 7",
				"Example 8", "Example 9", "Example 10");

		examples.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				Notification.show("No example selected");
			} else {
				if (event.getValue() == "Example 1") {
					//file.setValue("file:///C:/movies.rdf");
					editor.setValue(type0);
				} else if (event.getValue() == "Example 2") {
					//file.setValue("file:///C:/movies.rdf");
					editor.setValue(type1);
				} else if (event.getValue() == "Example 3") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(type2);
				} else if (event.getValue() == "Example 4") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(type3);
				} else if (event.getValue() == "Example 5") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(type4);
				} else if (event.getValue() == "Example 6") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(type5);
				}
				else if (event.getValue() == "Example 7") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(type6);
					
				}
				else if (event.getValue() == "Example 8") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(type7);
					
				}
				else if (event.getValue() == "Example 9") {
					//file.setValue("file:///C:/hotels.rdf");
					editor.setValue(val1);
					
				}
				else if (event.getValue() == "Example 10") {
					//file.setValue("file:///C:/movies.rdf");
					editor.setValue(val8);
					
				}
				 
			}
		});

		editor.setValue(type0);
		editor.setDescription("SPARQL Query");

		TextField result = new TextField();
		result.setHeight("300px");
		result.setWidth("2000px");
		
		 

		AceEditor editorOntology = new AceEditor();
		Panel edO = new Panel();
		edO.setSizeFull();

		 

		typing.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {  
				
				
				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				 
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				 
				PrintStream old = System.out;
				 
				System.setOut(ps);
				
				GlassBoxExplanation exp = null;
				HSTExplanationGenerator multExplanator = null;
				PelletReasonerFactory pfactory = new PelletReasonerFactory();
				Configuration configuration = new Configuration();
				configuration.throwInconsistentOntologyException = false;
				OWLReasoner reasoner = pfactory.createReasoner(ontology, configuration);
					
				TSPARQL t = new TSPARQL(manager,manager_rdf,manager_owl,ontology,ont_rdf,ont_owl,
						dataFactory,df_rdf,df_owl,exp,multExplanator,pfactory,reasoner,configuration);
				
				//TSPARQL t = new TSPARQL("social-network-2018.owl","rdf-vocabulary.owl","owl-vocabulary.owl");
				
				result.setValue("");
				
				SPARQL_TYPING(t,filet.getValue(),editor.getValue());
				
				// Put things back
				System.out.flush();
				System.setOut(old);
				// Show what happened
				
				result.setValue(baos.toString());
			}		 

		});
		checking.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {  

				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				
				 
				PrintStream old = System.out;
				 
				System.setOut(ps);
				
				GlassBoxExplanation exp = null;
				HSTExplanationGenerator multExplanator = null;
				PelletReasonerFactory pfactory = new PelletReasonerFactory();
				Configuration configuration = new Configuration();
				configuration.throwInconsistentOntologyException = false;
				OWLReasoner reasoner = pfactory.createReasoner(ontology, configuration);
				 
				TSPARQL t = new TSPARQL(manager,manager_rdf,manager_owl,ontology,ont_rdf,ont_owl,
						dataFactory,df_rdf,df_owl,exp,multExplanator,pfactory,reasoner,configuration);
				
				//TSPARQL t = new TSPARQL("social-network-2018.owl","rdf-vocabulary.owl","owl-vocabulary.owl");
				
				t.SPARQL_CHECKING(filet.getValue(),editor.getValue());
				
				// Put things back
				System.out.flush();
				System.setOut(old);
				// Show what happened
				
				result.setValue(baos.toString());
			}		 

		});
		testing.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {  

			}		 

		});

		edS.setContent(editor);
		resP.setContent(result);

		layout.addComponent(lab);
		layout.addComponent(examples);
		layout.addComponent(filet);
		layout.addComponent(edS);
		layout.addComponent(hlb);
		layout.addComponent(resP);
		

		 

		String ontology;
		try {
			ontology = readStringFromURL("file:///C:/"+filet.getValue());
			editorOntology.setValue(ontology);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			Notification.show(e.getMessage());
		}

		edO.setContent(editorOntology);
		editorOntology.setHeight("300px");
		editorOntology.setWidth("2000px");
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
	
	
	public void SPARQL_TYPING(TSPARQL t,String file,String query) {
		//,PelletReasonerFactory pfactory,Configuration configuration,
		//		OWLReasoner reasoner,GlassBoxExplanation exp, HSTExplanationGenerator multExplanator,OWLDataFactory dataFactory) {

			FileInputStream source = null;
			FileOutputStream dest = null;
			try {
				source = new FileInputStream(file);
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			try {
				dest = new FileOutputStream("tmp.owl");
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			byte[] buffer = new byte[1024];
			int length;
			try {
				while ((length = source.read(buffer)) > 0) {
					dest.write(buffer, 0, length);
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			List<List<String>> rules = t.SPARQL_ANALYSIS(file,query, 0);
			
			

			String r = "";
			
			if (reasoner.isConsistent())
				r = "true";
			else {
				
				exp = new GlassBoxExplanation(ontology, pfactory);
			    multExplanator = new HSTExplanationGenerator(exp);
			try {
				r = t.explanations(ontology,reasoner,dataFactory);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			}
			

			FileInputStream source2 = null;
			FileOutputStream dest2 = null;
			try {
				source2 = new FileInputStream("tmp.owl");
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			try {
				dest2 = new FileOutputStream(file);
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			byte[] buffer2 = new byte[1024];
			int length2;
			try {
				while ((length2 = source2.read(buffer2)) > 0) {
					dest2.write(buffer2, 0, length2);
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			if (!(r == "true"))
				{System.out.println("Unsuccessful Typing due to:");
				System.out.print(r);}
			else {System.out.println("Successful Typing");}
			
			 
		}
    @WebServlet(urlPatterns = "/*", name = "MyUIServlet", asyncSupported = true)
    @VaadinServletConfiguration(ui = MyUI2.class, productionMode = false)
    public static class MyUIServlet extends VaadinServlet {
    }
}
