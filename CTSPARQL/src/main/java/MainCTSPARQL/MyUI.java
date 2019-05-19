package MainCTSPARQL;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Scanner;
import java.util.Set;

import javax.servlet.annotation.WebServlet;

import org.apache.log4j.varia.NullAppender;
import org.jpl7.Term;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.vaadin.aceeditor.AceEditor;
import org.vaadin.aceeditor.AceMode;
import org.vaadin.aceeditor.AceTheme;

import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QueryParseException;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.Syntax;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.sparql.core.Var;
import com.vaadin.annotations.Theme;
import com.vaadin.annotations.VaadinServletConfiguration;
import com.vaadin.icons.VaadinIcons;
import com.vaadin.server.ThemeResource;
import com.vaadin.server.VaadinRequest;
import com.vaadin.server.VaadinServlet;
import com.vaadin.shared.Position;
import com.vaadin.ui.Button;
import com.vaadin.ui.Button.ClickEvent;
import com.vaadin.ui.ComboBox;
import com.vaadin.ui.Grid;
import com.vaadin.ui.HorizontalLayout;
import com.vaadin.ui.Image;
import com.vaadin.ui.ItemCaptionGenerator;
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
import com.vaadin.server.Page;

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

	
	 
	
	String current_ontology="social-network-2019.owl";
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
	
	ComboBox<String> ontologies = new ComboBox<String>();
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
	
		
		AceEditor editorOntology = new AceEditor();
		
		final VerticalLayout main = new VerticalLayout();		
		main.setMargin(false);
		Image lab = new Image(null, new ThemeResource("banner.jpg"));
		
		lab.setWidth("100%");
		lab.setHeight("200px");
	 
		ontologies.setItems("file:///C:/social-network-2019.owl","http://owl.man.ac.uk/2006/07/sssw/people.owl",
				"https://protege.stanford.edu/ontologies/camera.owl","https://protege.stanford.edu/ontologies/koala.owl",
				"https://protege.stanford.edu/ontologies/pizza/pizza.owl",
				"https://protege.stanford.edu/ontologies/travel.owl",
				"https://www.w3.org/TR/owl-guide/wine.rdf");
		ontologies.setEmptySelectionCaption("Please select an ontology:");
		ontologies.setWidth("100%");
		ontologies.setEmptySelectionAllowed(false);
		
		
		ontologies.addValueChangeListener(event -> {
		    if (event.getSource().isEmpty()) {
		       error("","Empty Selection");
		        
		    } else {
		        current_ontology = event.getValue();
		        String ontology="";
				try {
					ontology = readStringFromURL(current_ontology);
					editorOntology.setValue(ontology);
				} catch (IOException e) {
					System.out.println(e.getMessage());
					error("Error Loading Ontology",e.getMessage());
				}
		        
				try (PrintWriter out = new PrintWriter("C:/working_ontology.owl")) {
				    out.println(ontology);
				} catch (FileNotFoundException e2) {
					// TODO Auto-generated catch block
					System.out.println(e2.getMessage());
				}
		    }
		    
		});

		/*setErrorHandler(new ErrorHandler() {
            
            @Override
            public void error(com.vaadin.server.ErrorEvent event) {
            	 
                restore("C:/working_ontology.owl");
            }
            
        });*/
		
		VerticalLayout debug = new VerticalLayout();
		debug.setWidth("100%");
		debug.setHeight("100%");
		debug.setMargin(false);
		debug.setVisible(false);

		
		HorizontalLayout hlb = new HorizontalLayout();
		
		Button correctness = new Button("Correctness");
		correctness.setStyleName(ValoTheme.BUTTON_FRIENDLY);
		correctness.setIcon(VaadinIcons.AMBULANCE);  
		correctness.setWidth("100%");
		
		Button type_validity = new Button("Type Validity");
		type_validity.setStyleName(ValoTheme.BUTTON_PRIMARY);
		type_validity.setIcon(VaadinIcons.HEART);
		type_validity.setWidth("100%");
		
		Button run_type_validity = new Button("Run Type Validity");
		run_type_validity.setStyleName(ValoTheme.BUTTON_FRIENDLY);
		run_type_validity.setIcon(VaadinIcons.PLAY);	
		run_type_validity.setWidth("100%");
		
		HorizontalLayout hlt = new HorizontalLayout();
		hlb.addComponent(correctness);
		hlb.addComponent(type_validity);
		hlb.setWidth("100%");
		
		hlt.addComponent(cb_type_validity);
		hlt.addComponent(cb_vars);
		hlt.addComponent(run_type_validity);
		hlt.setWidth("100%");
		
		cb_type_validity.setVisible(false);
		cb_type_validity.setWidth("100%");
		cb_type_validity.setEmptySelectionAllowed(false);
		
		cb_vars.setVisible(false);
		cb_vars.setEmptySelectionAllowed(false);
		cb_vars.setWidth("100%");
		
		run_type_validity.setVisible(false);		
		
		Panel edS = new Panel();
		Panel resP = new Panel();
		
		Button run_button = new Button("Execute Query");
		run_button.setWidth("100%");
		run_button.setStyleName(ValoTheme.BUTTON_FRIENDLY);
		run_button.setIcon(VaadinIcons.PLAY);
		Button debug_button = new Button("Debug Query");
		debug_button.setWidth("100%");
		debug_button.setStyleName(ValoTheme.BUTTON_PRIMARY);
		debug_button.setIcon(VaadinIcons.TOOLS);
		
		
		
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
		
		// CORRECTNESS

		// First Method. Wrongly Typed Query.

		 
		String ex1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE { sn:foo sn:unknown sn:bad }\n";

		String ex2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:attends_to ?EVENT . \r\n"
				+ "?USER sn:friend_of ?EVENT\r\n" + "}";

		String ex3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE \r\n" + "{\r\n" + "?USER sn:attends_to ?USER\r\n" + "}\r\n" + "\r\n" + "";

		String ex4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE \r\n" + "{\r\n" + "?USER sn:likes ?EVENT\r\n ." + "?EVENT rdf:type sn:User\r\n"
				+ "}";

		String ex5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:attends_to ?EVENT . \r\n"
				+ "?USER sn:age ?EVENT\r\n" + "}\n";

		String ex6 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:age ?EVENT .\r\n"
				+ "?EVENT rdf:type sn:Event\r\n" + "}";

		String ex7 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:age ?EVENT .\r\n" + "?EVENT rdf:type ?TYPE\r\n"
				+ "}";

		String ex8 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?P ?EVENT WHERE \r\n" + "{\r\n" + "?USER ?P ?EVENT . \r\n" + "?USER sn:age ?P\r\n"
				+ "}";

		String ex9 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:Event .\r\n" + "?USER rdf:type sn:User  \r\n" + "}";

		String ex10 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:Event .\r\n" + "?USER rdf:type ?TYPE .\r\n"
				+ "?TYPE rdfs:subClassOf sn:User\r\n" + "}";

		String ex11 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type 10\r\n" + "}";

		String ex12 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?VALUE WHERE \r\n" + "{ \r\n" + "?USER sn:name ?VALUE .\r\n"
				+ "FILTER (?VALUE > 10) \r\n" + "}";

		String ex13 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?VALUE WHERE \r\n" + "{ \r\n" + "sn:jesus sn:name ?VALUE .\r\n"
				+ "FILTER (?VALUE > 10) \r\n" + "}";

		String ex14 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?NAME ?AGE WHERE \r\n" + "{ \r\n" + "sn:jesus sn:name ?NAME .\r\n"
				+ "sn:jesus sn:age ?NAME\r\n" + "}";

		String ex15 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?NAME ?AGE WHERE \r\n" + "{ \r\n" + "sn:jesus sn:name ?NAME .\r\n"
				+ "sn:jesus sn:age ?AGE .\r\n" + "FILTER (?NAME > ?AGE) \r\n" + "}";

		String ex16 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER ?PROP ?EVENT . \r\n" + "FILTER (?USER > 10)\r\n"
				+ "}";

		// First Method. Inconsistent Query.

	 
		String ex17 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE = 50) " + ". BIND ((?AGE+?AGE) AS ?U) "
				+ ". FILTER(?U = 10)}";

		String ex18 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER1 ?USER2 " + "WHERE {\n" + "?USER1 sn:age ?AU1 . " + "?USER2 sn:age ?AU2 . \n "
				+ "FILTER(?AU1-?AU2 < 10) .\n" + "FILTER(?AU1 > 40 ).\n" + "FILTER (?AU2 < 18) }\n";

		String ex19 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE {\n" + "?USER sn:age ?AU . " + "FILTER(?AU > 30 ).\n" + "FILTER (?AU < 31) }\n";

		String ex20 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE {\n" + "?USER sn:height ?HU  . " + "FILTER(?HU > 130 ).\n" + "FILTER (?HU < 131) }\n";

		String ex21 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:friend_of ?USER \r\n" + "}";

		String ex22 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE {\n" + "?USER sn:height ?H .\n" + "FILTER (?H > 175) .\n" + "FILTER EXISTS "
				+ "{SELECT ?USER2 WHERE {\n" + "?USER2 sn:height ?H2 .\n" + "FILTER (?H2 < 176) .\n"
				+ "FILTER (?H < ?H2 ) }\n" + "}}\n";

		String ex23 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "sn:jesus sn:friend_of sn:jesus\r\n" + "}";

		String ex24 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DA \r\n" + "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:Active . \r\n"
				+ "?USER sn:dailyActivity ?DA . \r\n" + "FILTER (?DA<=4) \r\n" + "}";

		String ex25 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "sn:jesus sn:age ?AGE .\r\n" + "FILTER (?AGE = 50) .\r\n"
				+ "FILTER (?AGE = 100)\r\n" + "}";

		String ex26 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:age ?AGE .\r\n" + "?USER2 sn:age ?AGE2 . \r\n"
				+ "FILTER (?AGE2 < 50) .\r\n" + "FILTER (?AGE > 100) .\r\n" + "BIND((?AGE + ?AGE2) AS ?SUM) .\r\n"
				+ "FILTER (?SUM < 10)\r\n" + "}";

		
		String ex27 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?MESSAGE\r\n" + "WHERE \r\n" + "{ \r\n" + "?MESSAGE sn:date ?DATE .\r\n"
				+ "FILTER (?DATE < '2017-09-04T01:00:00Z'^^xsd:dateTime) .\r\n"
				+ "FILTER (?DATE > '2017-09-04T01:00:00Z'^^xsd:dateTime)\r\n" + "}";

		String ex28 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER\r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:name ?NAME .\r\n" + "FILTER (?NAME < 'a') .\r\n"
				+ "FILTER (?NAME > 'z')\r\n" + "}";

		String ex29 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:age ?AGE .\r\n" + "?USER sn:age ?AGE2\r\n"
				+ "FILTER (?AGE != ?AGE2) \r\n" + "}";

		String ex30 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:OpinionLeader .\r\n" + "?USER sn:creates ?MESSAGE\r\n"
				+ "}";

		String ex31 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:SocialLeader .\r\n" + "?USER sn:creates ?MESSAGE\r\n"
				+ "}";

		// TYPE VALIDITY

		// Second Method. Incomplete Query. Missing Triple Pattern.
		
		String ex32 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE .\r\n"
				+ "?USER2 sn:likes ?MESSAGE\r\n" + "}";

		String ex33 = "# ?USER : sn:SocialLeader\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE .\r\n"
				+ "?USER2 sn:likes ?MESSAGE\r\n" + "}";

		String ex34 = "# ?USER : sn:SocialLeader\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:likes ?MESSAGE .\r\n"
				+ "?USER2 sn:shares ?MESSAGE\r\n" + "}";

		String ex35 = "# ?USER : sn:OpinionLeader\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE .\r\n" + "}";

		// Second Method. Incomplete Query. Missing Filter Condition.

		String ex36 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL \r\n" + "}";

		// Second Method. Inconsistent Variable Typing. Ontology Inconsistency.

		String ex37 = "# ?USER : sn:Message\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?MESSAGE sn:attends_to ?USER\r\n" + "}";

		String ex38 = "# ?USER : sn:User\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?MESSAGE sn:attends_to ?USER\r\n" + "}";

		// Second Method. Inconsistent Variable Typing. Constraint Inconsistency.

		String ex39 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL .\r\n" + "FILTER (?DL < 200) \r\n" + "}";
		
		String ex40 = "# ?USER : sn:Active\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DA \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyActivity ?DA .\r\n" + "FILTER (?DA < 200) \r\n" + "}";

		// Second Method. Counterexamples of Variable Typing.

		String ex41 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL .\r\n" + "FILTER (?DL > 200) \r\n" + "}";
			
		 
		ComboBox<String> examplest = new ComboBox<>("Examples of Typing");
		examplest.setWidth("100%");
		examplest.setEmptySelectionAllowed(false);
		examplest.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6", "Example 7",
				"Example 8", "Example 9", "Example 10","Example 11", "Example 12", "Example 13", "Example 14", "Example 15", 
				"Example 16", "Example 17",
				"Example 18", "Example 19", "Example 20","Example 21", "Example 22", "Example 23", "Example 24", 
				"Example 25", "Example 26", "Example 27",
				"Example 28", "Example 29", "Example 30","Example 31", "Example 32");
		
		examplest.setPageLength(32);
		
	 
		
		ComboBox<String> examplestst = new ComboBox<>("Examples of Type Validity");
		examplestst.setEmptySelectionAllowed(false);
		examplestst.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6", "Example 7",
				"Example 8", "Example 9");
		examplestst.setWidth("100%");

		examplest.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("","No Example Selected"); 
			} else {
				if (event.getValue() == "Example 1") {					 
					editor.setValue(ex1);
				} else if (event.getValue() == "Example 2") {					 
					editor.setValue(ex2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(ex3);
				} else if (event.getValue() == "Example 4") {
 					editor.setValue(ex4);
				} else if (event.getValue() == "Example 5") {					 
					editor.setValue(ex5);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(ex6);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(ex7);
				} else if (event.getValue() == "Example 8") {
 					editor.setValue(ex8);
				} else if (event.getValue() == "Example 9") {
					editor.setValue(ex9);
				} else if (event.getValue() == "Example 10") {				 
					editor.setValue(ex10);
				} else if
					(event.getValue() == "Example 11") {					 
					editor.setValue(ex11);
				} else if (event.getValue() == "Example 12") {					 
					editor.setValue(ex12);
				} else if (event.getValue() == "Example 13") {
					editor.setValue(ex13);
				} else if (event.getValue() == "Example 14") {
 					editor.setValue(ex14);
				} else if (event.getValue() == "Example 15") {					 
					editor.setValue(ex15);
				} else if (event.getValue() == "Example 16") {
					editor.setValue(ex16);
				} else if (event.getValue() == "Example 17") {
					editor.setValue(ex17);
				} else if (event.getValue() == "Example 18") {
 					editor.setValue(ex18);
				} else if (event.getValue() == "Example 19") {
					editor.setValue(ex19);
				} else if (event.getValue() == "Example 20") {				 
					editor.setValue(ex20);
				} else if
					(event.getValue() == "Example 21") {					 
					editor.setValue(ex21);
				} else if (event.getValue() == "Example 22") {					 
					editor.setValue(ex22);
				} else if (event.getValue() == "Example 23") {
					editor.setValue(ex23);
				} else if (event.getValue() == "Example 24") {
 					editor.setValue(ex24);
				} else if (event.getValue() == "Example 25") {					 
					editor.setValue(ex25);
				} else if (event.getValue() == "Example 26") {
					editor.setValue(ex26);
				} else if (event.getValue() == "Example 27") {
					editor.setValue(ex27);
				} else if (event.getValue() == "Example 28") {
 					editor.setValue(ex28);
				} else if (event.getValue() == "Example 29") {
					editor.setValue(ex29);
				} else if (event.getValue() == "Example 30") {				 
					editor.setValue(ex30);
				} else if (event.getValue() == "Example 31") {				 
					editor.setValue(ex31);}
					 else if (event.getValue() == "Example 32") {				 
							editor.setValue(ex32);
				}
				
			}
		});
		
		
		
		examplestst.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("","No Example Eelected");
				 
			} else {
				if (event.getValue() == "Example 1") {
 					editor.setValue(ex33);
				} else if (event.getValue() == "Example 2") {
 					editor.setValue(ex34);
				} else if (event.getValue() == "Example 3") {
 					editor.setValue(ex35);
				} else if (event.getValue() == "Example 4") {			 
					editor.setValue(ex36);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(ex37);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(ex38);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(ex39);
				} else if (event.getValue() == "Example 8") {
 					editor.setValue(ex40);
				} else if (event.getValue() == "Example 9") {
 					editor.setValue(ex41);
				}
				
			}
		});

		editor.setValue(ex1);
		editor.setDescription("SPARQL Query");
		
		TextArea result = new TextArea();
		result.setHeight("300px");
		result.setWidth("100%");
		result.setStyleName("multi-line-caption");
		
		Panel edO = new Panel();
		edO.setSizeFull();

		Grid<HashMap<String, RDFNode>> answers = new Grid<>();
		answers.setWidth("100%");
		List<HashMap<String, RDFNode>> rows = new ArrayList<>();
		 
		
		
		run_button.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {	
				OntModel model = ModelFactory.createOntologyModel();
				model.read("file:C://working_ontology.owl");
				com.hp.hpl.jena.query.Query query = QueryFactory.create(editor.getValue());
				ResultSet result = (ResultSet) QueryExecutionFactory.create(query, model).execSelect();
				answers.removeAllColumns();
				List<String> variables = result.getResultVars();
				rows.clear();
				while (result.hasNext())
				{
				QuerySolution solution = result.next();
				HashMap<String,RDFNode> sol = new HashMap<String,RDFNode>();
				for (String vari : variables)
				{
					sol.put(vari,solution.get(vari));
					 
				}
				rows.add(sol);
				}
				answers.setItems(rows);
				if (rows.size() > 0) {
					HashMap<String, RDFNode> sr = rows.get(0);
					 
					for (Map.Entry<String, RDFNode> entry : sr.entrySet()) {
						answers.addColumn(h -> h.get(entry.getKey())).setCaption(entry.getKey());
					}
				}
			}
		});
		
		debug_button.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {	
			if (!debug.isVisible()) {debug.setVisible(true); debug_button.setCaption("Close Debug");}
			else {debug.setVisible(false); debug_button.setCaption("Debug Query");}
			
			}
		});
		
		correctness.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {	
				result.setValue("");
				manager = OWLManager.createOWLOntologyManager();		
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/working_ontology.owl");
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {

					System.out.println(e2.getMessage());
					error("Error Loading Ontology",e2.getMessage());
				}
				manager_owl = OWLManager.createOWLOntologyManager();
				df_owl = manager_owl.getOWLDataFactory();
				ont_owl = null;
				File file_owl = new File(owl);
				try {
					ont_owl = manager_owl.loadOntologyFromOntologyDocument(file_owl);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontology",e2.getMessage());
				}

				manager_rdf = OWLManager.createOWLOntologyManager();
				df_rdf = manager_rdf.getOWLDataFactory();
				ont_rdf = null;
				File file_rdf = new File(rdf);
				try {
					ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontologgy",e2.getMessage());
				}
				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				PrintStream old = System.out;
				System.setOut(ps);
				TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
						df_rdf, df_owl,"C:/working_ontology.owl");
				long startTime = System.currentTimeMillis();
				try {
					t.SPARQL_CORRECTNESS(editor.getValue());
				} catch (Exception e) {
					// TODO Auto-generated catch block
					error("Error Loading Query",e.getMessage());
					
				}
				long estimatedTime = System.currentTimeMillis() - startTime;
				System.out.println("");
				System.out.println("Analysis done in " +estimatedTime + " ms");
				System.out.flush();
				System.setOut(old);
				result.setValue(baos.toString());
				System.out.println(baos.toString());
			}
		});
		 
		type_validity.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {		
				result.setValue("");
				manager = OWLManager.createOWLOntologyManager();
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/working_ontology.owl");
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontology",e2.getMessage());
				}		
				cb_type_validity.clear();
				cb_vars.clear();			
				cb_type_validity.setVisible(true);
				cb_vars.setVisible(true);
				run_type_validity.setVisible(true);			
				Set<OWLClass> classes_type_validity = ontology.getClassesInSignature();
				List<String> names = new ArrayList<String>();
				String urio = ontology.getOntologyID().getOntologyIRI().toString();
				for (OWLClass c:classes_type_validity)
				{
				if (c.getIRI().getStart().equals(urio+"#")
						) {names.add(c.getIRI().toString());}
				}
				cb_type_validity.setItems(names);				
				com.hp.hpl.jena.query.Query query = QueryFactory.create(editor.getValue());
				List<Var> vars = query.getProjectVars();
				cb_vars.setItems(vars);
				type_validity.setEnabled(false);
				correctness.setEnabled(false);
				 
			}
		});
		
		run_type_validity.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {		
				if (cb_type_validity.isEmpty() || cb_vars.isEmpty())
				{
					error("","Please select a class and an individual");
					 
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
					System.out.println(e2.getMessage());
					error("Error Loading Ontology",e2.getMessage());
				}
				manager_rdf = OWLManager.createOWLOntologyManager();
				df_rdf = manager_rdf.getOWLDataFactory();
				ont_rdf = null;
				File file_rdf = new File(rdf);
				try {
					ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontology",e2.getMessage());
				}
				org.apache.log4j.BasicConfigurator.configure(new NullAppender());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				PrintStream old = System.out;
				System.setOut(ps);	 
				TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
						df_rdf, df_owl,"C:/working_ontology.owl");
				Optional<Var> variable_type_validity = cb_vars.getSelectedItem();
				Optional<String> type_type_validity = cb_type_validity.getSelectedItem();
				String var_name = variable_type_validity.get().getName().replace('?', ' ').replaceAll("\\s", "");  
				String type_name = type_type_validity.get();		
				long startTime = System.currentTimeMillis();
				
				 
				
				try {
					t.SPARQL_TYPE_VALIDITY(editor.getValue(),var_name,type_name);
				} catch (Exception e) {
					// TODO Auto-generated catch block
					error("Error Loading Query",e.getMessage());
					 

				}		
				cb_type_validity.setVisible(false);
				cb_vars.setVisible(false);
				run_type_validity.setVisible(false);	
				type_validity.setEnabled(true);
				 
				correctness.setEnabled(true);
				long estimatedTime = System.currentTimeMillis() - startTime;
				System.out.println("");
				System.out.println("Analysis done in " +estimatedTime + " ms");
				System.out.flush();
				System.setOut(old);
				result.setValue(baos.toString());
			}
			}
		});
		
		edS.setContent(editor);
		resP.setContent(result);
		HorizontalLayout examplesall = new HorizontalLayout();
		
		
		main.addComponent(lab);
		main.setWidth("100%");
		
		examplesall.setWidth("100%");
		examplesall.addComponent(examplest); 
		examplesall.addComponent(examplestst);
		
		main.addComponent(ontologies);
		main.addComponent(examplesall);	
		
		
		
		
		main.addComponent(edS);
		main.addComponent(run_button);
	    main.addComponent(debug_button);
	    main.addComponent(answers);
		
		debug.addComponent(hlb);
		debug.addComponent(hlt);
		debug.addComponent(resP);
		
		main.addComponent(debug);
		
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
		
		main.addComponent(edO);
		setContent(main);
		this.setSizeFull();
	}
	
	public void restore(String file) {
		FileInputStream source2 = null;
		FileOutputStream dest2 = null;
		try {
			source2 = new FileInputStream("tmp.owl");
		} catch (FileNotFoundException e) {
			System.out.println(e.getMessage());
		}
		try {
			dest2 = new FileOutputStream(file);
		} catch (FileNotFoundException e) {
			System.out.println(e.getMessage());
		}
		byte[] buffer2 = new byte[1024];
		int length2;
		try {
			while ((length2 = source2.read(buffer2)) > 0) {
				dest2.write(buffer2, 0, length2);
			}
		} catch (IOException e) {
			System.out.println(e.getMessage());
		}

	};
	
	public void error(String type, String message)
	{
		Notification notif = new Notification(
	        	type,
	                    message,
	                    Notification.Type.ERROR_MESSAGE);
		notif.setDelayMsec(20000);
    	notif.setPosition(Position.BOTTOM_RIGHT);
    	notif.show(Page.getCurrent());
	}
	@WebServlet(urlPatterns = "/*", name = "MyUIServlet", asyncSupported = true)
	@VaadinServletConfiguration(ui = MyUI.class, productionMode = false)
	public static class MyUIServlet extends VaadinServlet {
	}
}
