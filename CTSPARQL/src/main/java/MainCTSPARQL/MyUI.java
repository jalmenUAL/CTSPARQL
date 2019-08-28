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

import org.apache.jena.ontology.OntModel;
import org.apache.jena.query.Query;
import org.apache.jena.query.QueryExecutionFactory;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.QuerySolution;
import org.apache.jena.query.ResultSet;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.sparql.core.Var;
//import org.apache.log4j.varia.NullAppender;
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

//import com.hp.hpl.jena.ontology.OntModel;
//import com.hp.hpl.jena.query.QueryExecutionFactory;
//import com.hp.hpl.jena.query.QueryFactory;
//import com.hp.hpl.jena.query.QuerySolution;
//import com.hp.hpl.jena.query.ResultSet;
//import com.hp.hpl.jena.rdf.model.ModelFactory;
//import com.hp.hpl.jena.rdf.model.RDFNode;
//import com.hp.hpl.jena.sparql.core.Var;
import com.vaadin.annotations.Theme;
import com.vaadin.annotations.VaadinServletConfiguration;
import com.vaadin.event.ShortcutAction;
import com.vaadin.event.ShortcutListener;
import com.vaadin.icons.VaadinIcons;
import com.vaadin.server.ErrorHandler;
import com.vaadin.server.ExternalResource;
import com.vaadin.server.Page;
import com.vaadin.server.ThemeResource;
import com.vaadin.server.VaadinRequest;
import com.vaadin.server.VaadinServlet;
import com.vaadin.shared.Position;
import com.vaadin.ui.BrowserFrame;
import com.vaadin.ui.Button;
import com.vaadin.ui.Button.ClickEvent;
import com.vaadin.ui.ComboBox;
import com.vaadin.ui.Embedded;
import com.vaadin.ui.Grid;
import com.vaadin.ui.HorizontalLayout;
import com.vaadin.ui.Image;
import com.vaadin.ui.Notification;
import com.vaadin.ui.Panel;
import com.vaadin.ui.RichTextArea;
import com.vaadin.ui.TextArea;
import com.vaadin.ui.TextField;
import com.vaadin.ui.UI;
import com.vaadin.ui.VerticalLayout;
import com.vaadin.ui.themes.ValoTheme;

import CTSPARQL.TSPARQL;

//SELECT NO VARIABLE IN NESTED EXPRESSIONS IS NOT HANDLED
//SUBPROPERTY IS NOT HANDLED
//MIXED INTEGERS AND REALS ARE NOT HANDLED 
//EJEMPLOS NUEVOS

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
	String current_ontology = "sn-2019.owl";
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

	ComboBox<String> ontologies = new ComboBox<String>("Examples of Ontologies");
	ComboBox<String> cb_type_validity = new ComboBox<String>();
	ComboBox<Var> cb_vars = new ComboBox<Var>();
	TextField new_ontology = new TextField("Type URL of an ontology");
	

	public static String readStringFromURL(String requestURL) throws IOException {
		try (Scanner scanner = new Scanner(new URL(requestURL).openStream(), StandardCharsets.UTF_8.toString())) {
			scanner.useDelimiter("\\A");
			return scanner.hasNext() ? scanner.next() : "";
		}
	}

	@Override
	protected void init(VaadinRequest vaadinRequest) {
		//AceEditor embedded = new AceEditor();
		
		BrowserFrame embedded = new BrowserFrame("html");
		 
		
		final VerticalLayout main = new VerticalLayout();
		main.setMargin(false);
		Image lab = new Image(null, new ThemeResource("banner.jpg"));
		lab.setWidth("100%");
		lab.setHeight("200px");
		ontologies.setItems("http://minerva.ual.es:8080/ontologies/sn-2019.owl", "http://minerva.ual.es:8080/ontologies/course.owl", 
				"http://minerva.ual.es:8080/ontologies/conference.owl",
				"http://owl.man.ac.uk/2006/07/sssw/people.owl",
				"https://protege.stanford.edu/ontologies/pizza/pizza.owl");
		ontologies.setEmptySelectionCaption("Please select an ontology:");
		ontologies.setWidth("100%");
		new_ontology.setWidth("100%");
		
/*
	   setErrorHandler(new ErrorHandler() {

			@Override
			public void error(com.vaadin.server.ErrorEvent event) {

				restore("C:/working_ontology.owl");
			}

		});
*/

		VerticalLayout debug = new VerticalLayout();

		debug.setWidth("100%");
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
		run_type_validity.setVisible(false);

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

		Panel edS = new Panel("SPARQL Query");
		Panel resP = new Panel("Debugging Result");

		Button run_button = new Button("Execute Query");

		run_button.setWidth("100%");
		run_button.setStyleName(ValoTheme.BUTTON_FRIENDLY);
		run_button.setIcon(VaadinIcons.PLAY);
		run_button.setVisible(false);

		Button debug_button = new Button("Debug Query");

		debug_button.setWidth("100%");
		debug_button.setStyleName(ValoTheme.BUTTON_PRIMARY);
		debug_button.setIcon(VaadinIcons.TOOLS);
		debug_button.setVisible(false);

		edS.setSizeFull();
		resP.setWidth("100%");
		resP.setHeight("100%");
		resP.setVisible(false);

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

		Grid<HashMap<String, RDFNode>> answers = new Grid<>("Execution Result");
		answers.setWidth("100%");
		answers.setHeight("100%");
		answers.setVisible(false);

		// SOCIAL NETWORK

		// CORRECTNESS

		// First Method. Wrongly Typed Query.

		String socex1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE { sn:foo sn:unknown sn:bad }\n";

		String socex2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:attends_to ?EVENT . \r\n"
				+ "?USER sn:friend_of ?EVENT\r\n" + "}";

		String socex3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE \r\n" + "{\r\n" + "?USER sn:attends_to ?USER\r\n" + "}\r\n" + "\r\n" + "";

		String socex4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE \r\n" + "{\r\n" + "?USER sn:likes ?EVENT\r\n ." + "?EVENT rdf:type sn:User\r\n"
				+ "}";

		String socex5 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:attends_to ?EVENT . \r\n"
				+ "?USER sn:age ?EVENT\r\n" + "}\n";

		String socex6 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:age ?EVENT .\r\n"
				+ "?EVENT rdf:type sn:Event\r\n" + "}";

		String socex7 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER sn:age ?EVENT .\r\n" + "?EVENT rdf:type ?TYPE\r\n"
				+ "}";

		String socex8 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?P ?EVENT WHERE \r\n" + "{\r\n" + "?USER ?P ?EVENT . \r\n" + "?USER sn:age ?P\r\n"
				+ "}";

		String socex9 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:Event .\r\n" + "?USER rdf:type sn:User  \r\n" + "}";

		String socex10 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:Event .\r\n" + "?USER rdf:type ?TYPE .\r\n"
				+ "?TYPE rdfs:subClassOf sn:User\r\n" + "}";

		String socex11 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type 10\r\n" + "}";

		String socex12 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?VALUE WHERE \r\n" + "{ \r\n" + "?USER sn:name ?VALUE .\r\n"
				+ "FILTER (?VALUE > 10) \r\n" + "}";

		String socex13 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?VALUE WHERE \r\n" + "{ \r\n" + "sn:jesus sn:name ?VALUE .\r\n"
				+ "FILTER (?VALUE > 10) \r\n" + "}";

		String socex14 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?NAME ?AGE WHERE \r\n" + "{ \r\n" + "sn:jesus sn:name ?NAME .\r\n"
				+ "sn:jesus sn:age ?NAME\r\n" + "}";

		String socex15 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?NAME ?AGE WHERE \r\n" + "{ \r\n" + "sn:jesus sn:name ?NAME .\r\n"
				+ "sn:jesus sn:age ?AGE .\r\n" + "FILTER (?NAME > ?AGE) \r\n" + "}";

		String socex16 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?EVENT WHERE \r\n" + "{\r\n" + "?USER ?PROP ?EVENT . \r\n" + "FILTER (?USER > 10)\r\n"
				+ "}";

		// First Method. Inconsistent Query.

		String socex17 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE = 50) " + ". BIND ((?AGE+?AGE) AS ?U) "
				+ ". FILTER(?U = 10)}";

		String socex18 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER1 ?USER2 " + "WHERE {\n" + "?USER1 sn:age ?AU1 . " + "?USER2 sn:age ?AU2 . \n "
				+ "FILTER(?AU1-?AU2 < 10) .\n" + "FILTER(?AU1 > 40 ).\n" + "FILTER (?AU2 < 18) }\n";

		String socex19 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE {\n" + "?USER sn:age ?AU . " + "FILTER(?AU > 30 ).\n" + "FILTER (?AU < 31) }\n";

		String socex20 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE {\n" + "?USER sn:height ?HU  . " + "FILTER(?HU > 130 ).\n" + "FILTER (?HU < 131) }\n";

		String socex21 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:friend_of ?USER \r\n" + "}";

		String socex22 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE {\n" + "?USER sn:height ?H .\n" + "FILTER (?H > 175) .\n" + "FILTER EXISTS "
				+ "{SELECT ?USER2 WHERE {\n" + "?USER2 sn:height ?H2 .\n" + "FILTER (?H2 < 176) .\n"
				+ "FILTER (?H < ?H2 ) }\n" + "}}\n";

		String socex23 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "sn:jesus sn:friend_of sn:jesus\r\n" + "}";

		String socex24 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DA \r\n" + "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:Active . \r\n"
				+ "?USER sn:dailyActivity ?DA . \r\n" + "FILTER (?DA<=4) \r\n" + "}";

		String socex25 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "sn:jesus sn:age ?AGE .\r\n" + "FILTER (?AGE = 50) .\r\n"
				+ "FILTER (?AGE = 100)\r\n" + "}";

		String socex26 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:age ?AGE .\r\n" + "?USER2 sn:age ?AGE2 . \r\n"
				+ "FILTER (?AGE2 < 50) .\r\n" + "FILTER (?AGE > 100) .\r\n" + "BIND((?AGE + ?AGE2) AS ?SUM) .\r\n"
				+ "FILTER (?SUM < 10)\r\n" + "}";

		String socex27 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?MESSAGE\r\n" + "WHERE \r\n" + "{ \r\n" + "?MESSAGE sn:date ?DATE .\r\n"
				+ "FILTER (?DATE < '2017-09-04T01:00:00Z'^^xsd:dateTime) .\r\n"
				+ "FILTER (?DATE > '2017-09-04T01:00:00Z'^^xsd:dateTime)\r\n" + "}";

		String socex28 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER\r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:name ?NAME .\r\n" + "FILTER (?NAME < 'a') .\r\n"
				+ "FILTER (?NAME > 'z')\r\n" + "}";

		String socex29 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER sn:age ?AGE .\r\n" + "?USER sn:age ?AGE2\r\n"
				+ "FILTER (?AGE != ?AGE2) \r\n" + "}";

		String socex30 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:OpinionLeader .\r\n" + "?USER sn:creates ?MESSAGE\r\n"
				+ "}";

		String socex31 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER \r\n"
				+ "WHERE \r\n" + "{ \r\n" + "?USER rdf:type sn:SocialLeader .\r\n" + "?USER sn:creates ?MESSAGE\r\n"
				+ "}";

		// TYPE VALIDITY

		// Second Method. Incomplete Query. Missing Triple Pattern.

		String socex32 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE .\r\n"
				+ "?USER2 sn:likes ?MESSAGE\r\n" + "}";

		String socex33 = "# ?USER : sn:SocialLeader\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE .\r\n"
				+ "?USER2 sn:likes ?MESSAGE\r\n" + "}";

		String socex34 = "# ?USER : sn:SocialLeader\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:likes ?MESSAGE .\r\n"
				+ "?USER2 sn:shares ?MESSAGE\r\n" + "}";

		String socex35 = "# ?USER : sn:OpinionLeader\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE .\r\n" + "}";

		// Second Method. Incomplete Query. Missing Filter Condition.

		String socex36 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL \r\n" + "}";

		// Second Method. Inconsistent Variable Typing. Ontology Inconsistency.

		String socex37 = "# ?USER : sn:Message\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?MESSAGE sn:attends_to ?USER\r\n" + "}";

		String socex38 = "# ?USER : sn:User\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?MESSAGE sn:attends_to ?USER\r\n" + "}";

		// Second Method. Inconsistent Variable Typing. Constraint Inconsistency.

		String socex39 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL .\r\n" + "FILTER (?DL < 200) \r\n" + "}";

		String socex40 = "# ?USER : sn:Active\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DA \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyActivity ?DA .\r\n" + "FILTER (?DA < 200) \r\n" + "}";

		// Second Method. Counterexamples of Variable Typing.

		String socex41 = "# ?USER : sn:Influencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL .\r\n" + "FILTER (?DL > 200) \r\n" + "}";

		ComboBox<String> examplestsocial = new ComboBox<>("Examples of Correctness");
		examplestsocial.setWidth("100%");
		examplestsocial.setEmptySelectionAllowed(false);
		examplestsocial.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6",
				"Example 7", "Example 8", "Example 9", "Example 10", "Example 11", "Example 12", "Example 13",
				"Example 14", "Example 15", "Example 16", "Example 17", "Example 18", "Example 19", "Example 20",
				"Example 21", "Example 22", "Example 23", "Example 24", "Example 25", "Example 26", "Example 27",
				"Example 28", "Example 29", "Example 30", "Example 31", "Example 32");
		examplestsocial.setPageLength(32);

		ComboBox<String> examplestvsocial = new ComboBox<>("Examples of Type Validity");
		examplestvsocial.setEmptySelectionAllowed(false);
		examplestvsocial.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6",
				"Example 7", "Example 8", "Example 9");
		examplestvsocial.setWidth("100%");
		examplestvsocial.setPageLength(9);

		examplestsocial.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("", "No Example Selected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);

				if (event.getValue() == "Example 1") {
					editor.setValue(socex1);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(socex2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(socex3);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(socex4);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(socex5);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(socex6);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(socex7);
				} else if (event.getValue() == "Example 8") {
					editor.setValue(socex8);
				} else if (event.getValue() == "Example 9") {
					editor.setValue(socex9);
				} else if (event.getValue() == "Example 10") {
					editor.setValue(socex10);
				} else if (event.getValue() == "Example 11") {
					editor.setValue(socex11);
				} else if (event.getValue() == "Example 12") {
					editor.setValue(socex12);
				} else if (event.getValue() == "Example 13") {
					editor.setValue(socex13);
				} else if (event.getValue() == "Example 14") {
					editor.setValue(socex14);
				} else if (event.getValue() == "Example 15") {
					editor.setValue(socex15);
				} else if (event.getValue() == "Example 16") {
					editor.setValue(socex16);
				} else if (event.getValue() == "Example 17") {
					editor.setValue(socex17);
				} else if (event.getValue() == "Example 18") {
					editor.setValue(socex18);
				} else if (event.getValue() == "Example 19") {
					editor.setValue(socex19);
				} else if (event.getValue() == "Example 20") {
					editor.setValue(socex20);
				} else if (event.getValue() == "Example 21") {
					editor.setValue(socex21);
				} else if (event.getValue() == "Example 22") {
					editor.setValue(socex22);
				} else if (event.getValue() == "Example 23") {
					editor.setValue(socex23);
				} else if (event.getValue() == "Example 24") {
					editor.setValue(socex24);
				} else if (event.getValue() == "Example 25") {
					editor.setValue(socex25);
				} else if (event.getValue() == "Example 26") {
					editor.setValue(socex26);
				} else if (event.getValue() == "Example 27") {
					editor.setValue(socex27);
				} else if (event.getValue() == "Example 28") {
					editor.setValue(socex28);
				} else if (event.getValue() == "Example 29") {
					editor.setValue(socex29);
				} else if (event.getValue() == "Example 30") {
					editor.setValue(socex30);
				} else if (event.getValue() == "Example 31") {
					editor.setValue(socex31);
				} else if (event.getValue() == "Example 32") {
					editor.setValue(socex32);
				}

			}
		});

		examplestvsocial.addValueChangeListener(event -> {

			if (event.getSource().isEmpty()) {
				error("", "No Example Eelected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(socex33);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(socex34);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(socex35);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(socex36);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(socex37);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(socex38);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(socex39);
				} else if (event.getValue() == "Example 8") {
					editor.setValue(socex40);
				} else if (event.getValue() == "Example 9") {
					editor.setValue(socex41);
				}
			}
		});

		// SOCIAL NETWORK

		// PEOPLE

		String peoplex1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?A WHERE {?A rdf:type pp:dog . ?A rdf:type pp:cat}\r\n" + "";

		String peoplex2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE {?P rdf:type pp:kid . ?P rdf:type pp:adult}\r\n" + "";

		String peoplex3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?A WHERE {?A rdf:type pp:animal . ?A pp:part_of ?plant . ?plant rdf:type pp:plant}\r\n" + "";

		String peoplex4 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?L WHERE {?L rdf:type pp:old_lady . ?L pp:has_pet ?P . ?P rdf:type pp:dog}\r\n" + "";

		String peoplex5 = "# ?D : driver\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?D WHERE  {?D rdf:type pp:person}\r\n" + "";

		String peoplex6 = "# ?P : driver\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:adult . ?P rdf:type pp:male}";

		String peoplex7 = "# ?P : Vegetarian\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?A WHERE  {?A rdf:type pp:adult . ?A pp:eats pp:Rex}\r\n" + "";

		String peoplex8 = "# ?W : old_lady\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?W WHERE  {?W rdf:type pp:woman}\r\n";

		String peoplex9 = "# ?P : dog_liker\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person . ?P pp:has_pet ?A}\r\n";

		String peoplex10 = "# ?P:grownup\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person}\r\n";

		String peoplex11 = "# ?P:old_lady\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person . ?P pp:has_pet ?A . ?A rdf:type pp:animal}\r\n" + "";

		String peoplex12 = "# ?P:vegetarian\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person}\r\n" + "";

		String peoplex13 = "# ?P:tabloid\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:newspaper}";

		ComboBox<String> examplestpeople = new ComboBox<>("Examples of Correctness");
		examplestpeople.setWidth("100%");
		examplestpeople.setEmptySelectionAllowed(false);
		examplestpeople.setItems("Example 1", "Example 2", "Example 3", "Example 4");
		examplestpeople.setPageLength(4);

		ComboBox<String> examplestvpeople = new ComboBox<>("Examples of Type Validity");
		examplestvpeople.setEmptySelectionAllowed(false);
		examplestvpeople.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6",
				"Example 7", "Example 8", "Example 9");
		examplestvpeople.setWidth("100%");
		examplestvpeople.setPageLength(9);

		examplestpeople.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("", "No Example Selected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(peoplex1);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(peoplex2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(peoplex3);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(peoplex4);
				}

			}
		});
		examplestvpeople.addValueChangeListener(event -> {

			if (event.getSource().isEmpty()) {
				error("", "No Example Eelected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);

				if (event.getValue() == "Example 1") {
					editor.setValue(peoplex5);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(peoplex6);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(peoplex7);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(peoplex8);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(peoplex9);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(peoplex10);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(peoplex11);
				} else if (event.getValue() == "Example 8") {
					editor.setValue(peoplex12);
				} else if (event.getValue() == "Example 9") {
					editor.setValue(peoplex13);
				}
			}
		});

		// PEOPLE

		// PIZZA

		String pizz1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:SpicyPizza .  ?P rdf:type pi:Margherita}\r\n" + "";

		String pizz2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:MeatyPizza .  ?P pi:hasTopping pi:FruitTopping }\r\n" + "";

		String pizz3 = "# ?P:Mushroom\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:MeatyPizza .  ?P pi:hasTopping pi:FruitTopping }\r\n" + "";

		String pizz4 = "# ?P:ThinAndCrispyPizza\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:MeatyPizza .  ?X pi:hasTopping pi:FruitTopping }\r\n" + "";

		String pizz5 = "# ?P:AmericanHot\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:NamedPizza .  ?X pi:hasSpiciness pi:Medium }\r\n" + "";

		ComboBox<String> examplestpizza = new ComboBox<>("Examples of Correctness");
		examplestpizza.setWidth("100%");
		examplestpizza.setEmptySelectionAllowed(false);
		examplestpizza.setItems("Example 1", "Example 2");
		examplestpizza.setPageLength(2);

		ComboBox<String> examplestvpizza = new ComboBox<>("Examples of Type Validity");
		examplestvpizza.setEmptySelectionAllowed(false);
		examplestvpizza.setItems("Example 1", "Example 2", "Example 3");
		examplestvpizza.setWidth("100%");
		examplestvpizza.setPageLength(3);

		examplestpizza.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("", "No Example Selected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(pizz1);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(pizz2);
				}

			}
		});
		examplestvpizza.addValueChangeListener(event -> {

			if (event.getSource().isEmpty()) {
				error("", "No Example Eelected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(pizz3);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(pizz4);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(pizz5);
				}
			}
		});

		// COURSE

		String c1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S rdf:type co:professor}";

		String c2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E rdf:type co:passed . ?E rdf:type co:failed}";

		String c3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E rdf:type co:failed . ?E co:scores ?V . FILTER (?V > 5)}";

		String c4 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E rdf:type co:passed}";

		String c5 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E rdf:type co:failed}";

		String c6 = "# ?S: student\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S \r\n"
				+ "WHERE { ?S rdf:type co:person }";

		String c7 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S co:is_enrolled ?E . ?E co:scores ?V }";

		String c8 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S co:is_enrolled ?E . ?E co:scores ?V . FILTER (?V >= 3) }";

		String c9 = "# ?E: failed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S co:is_enrolled ?E . ?E co:scores ?V . FILTER (?V >= 3) }";

		ComboBox<String> examplestcourse = new ComboBox<>("Examples of Correctness");
		examplestcourse.setWidth("100%");
		examplestcourse.setEmptySelectionAllowed(false);
		examplestcourse.setItems("Example 1", "Example 2", "Example 3", "Example 4");
		examplestcourse.setPageLength(4);

		ComboBox<String> examplestvcourse = new ComboBox<>("Examples of Type Validity");
		examplestvcourse.setEmptySelectionAllowed(false);
		examplestvcourse.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5");
		examplestvcourse.setWidth("100%");
		examplestvcourse.setPageLength(5);

		examplestcourse.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("", "No Example Selected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(c1);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(c2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(c3);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(c4);
				}

			}
		});
		examplestvcourse.addValueChangeListener(event -> {

			if (event.getSource().isEmpty()) {
				error("", "No Example Eelected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(c5);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(c6);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(c7);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(c8);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(c9);
				}
			}
		});

		// CONFERENCE

		String con1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type con:acceptance . ?P rdf:type con:rejection  }";

		String con2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P \r\n"
				+ "WHERE { ?P rdf:type con:acceptance . ?P con:has_review ?R . ?R con:score ?V . FILTER (?V < 1)  }";

		String con3 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A \r\n"
				+ "WHERE { ?A rdf:type con:attendant . ?A con:submits ?P . ?P rdf:type con:rejection  }";

		String con4 = "# ?A : attendant\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A \r\n"
				+ "WHERE { ?A con:submits ?P  }";

		String con5 = "# ?A : attendant\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P con:has_review ?R  }";

		String con6 = "# ?P : acceptance\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P rdf:type con:paper  }";

		String con7 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P rdf:type con:paper  }";

		String con8 = "# ?A : attendant\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P rdf:type con:acceptance  }";

		String con9 = "# ?P : acceptance\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P con:has_review ?R . ?R con:score ?V . FILTER (?V > 2) }";

		String con10 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P con:has_review ?R . ?R con:score ?V . FILTER (?V > 0) }";

		String con11 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P con:has_review ?R }";

		ComboBox<String> examplestconf = new ComboBox<>("Examples of Correctness");
		examplestconf.setWidth("100%");
		examplestconf.setEmptySelectionAllowed(false);
		examplestconf.setItems("Example 1", "Example 2", "Example 3");
		examplestconf.setPageLength(4);

		ComboBox<String> examplestvconf = new ComboBox<>("Examples of Type Validity");
		examplestvconf.setEmptySelectionAllowed(false);
		examplestvconf.setItems("Example 1", "Example 2", "Example 3", "Example 4", "Example 5", "Example 6",
				"Example 7", "Example 8");
		examplestvconf.setWidth("100%");
		examplestvconf.setPageLength(8);

		examplestconf.addValueChangeListener(event -> {
			if (event.getSource().isEmpty()) {
				error("", "No Example Selected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(con1);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(con2);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(con3);
				}

			}
		});
		examplestvconf.addValueChangeListener(event -> {

			if (event.getSource().isEmpty()) {
				error("", "No Example Eelected. Please select an example.");
			} else {
				run_button.setVisible(true);
				debug_button.setVisible(true);
				if (event.getValue() == "Example 1") {
					editor.setValue(con4);
				} else if (event.getValue() == "Example 2") {
					editor.setValue(con5);
				} else if (event.getValue() == "Example 3") {
					editor.setValue(con6);
				} else if (event.getValue() == "Example 4") {
					editor.setValue(con7);
				} else if (event.getValue() == "Example 5") {
					editor.setValue(con8);
				} else if (event.getValue() == "Example 6") {
					editor.setValue(con9);
				} else if (event.getValue() == "Example 7") {
					editor.setValue(con10);
				} else if (event.getValue() == "Example 8") {
					editor.setValue(con11);
				}
			}
		});

		HorizontalLayout examplesall = new HorizontalLayout();
		examplesall.setWidth("100%");

		RichTextArea result = new RichTextArea();
		result.setReadOnly(true);
		result.setWidth("100%");
		result.setHeight("100%");
		result.setStyleName("multi-line-caption");
		result.setVisible(true);
		
		ShortcutListener shortcut = new ShortcutListener("", ShortcutAction.KeyCode.ENTER, null) {
			@Override
			public void handleAction(Object sender, Object target) {
				
				 
				ontologies.setValue(null);
				current_ontology = new_ontology.getValue();
				String ontology = "";
				editor.setValue("");
				examplesall.removeAllComponents();

				try {
					ontology = readStringFromURL(current_ontology);
					try (PrintWriter out = new PrintWriter("C:/working_ontology.owl")) {
						out.println(ontology);
					} catch (FileNotFoundException e2) {
						// TODO Auto-generated catch block
						System.out.println(e2.getMessage());
					}

					ExternalResource tr = new ExternalResource("http://minerva.ual.es:8090/webvowl_1.1.4/#iri="+current_ontology);
					embedded.setSource(tr);
				} catch (IOException e) {
					System.out.println(e.getMessage());
					error("Error Loading Ontology. Causes:", e.getMessage());
				}

			}
		};
		
		new_ontology.addShortcutListener(shortcut);
		new_ontology.setDescription("Type an ontology");
 		
		 
			
		ontologies.addValueChangeListener(event -> {

			if (event.getSource().isEmpty()) {
				//error("", "Empty Selection. Please select an ontology.");
			} else {
				new_ontology.setValue("");
				current_ontology = event.getValue();
				String ontology = "";
				editor.setValue("");

				try {
					ontology = readStringFromURL(current_ontology);
					try (PrintWriter out = new PrintWriter("C:/working_ontology.owl")) {
						out.println(ontology);
					} catch (FileNotFoundException e2) {
						// TODO Auto-generated catch block
						System.out.println(e2.getMessage());
					}

					ExternalResource tr = new ExternalResource("http://minerva.ual.es:8090/webvowl_1.1.4/#iri="+current_ontology);
					embedded.setSource(tr);

					if (current_ontology == "http://minerva.ual.es:8080/ontologies/sn-2019.owl") {
						examplesall.removeAllComponents();
						examplesall.addComponent(examplestsocial);
						examplesall.addComponent(examplestvsocial);
					}
					if (current_ontology == "http://owl.man.ac.uk/2006/07/sssw/people.owl") {
						examplesall.removeAllComponents();
						examplesall.addComponent(examplestpeople);
						examplesall.addComponent(examplestvpeople);
					}
					if (current_ontology == "https://protege.stanford.edu/ontologies/pizza/pizza.owl") {
						examplesall.removeAllComponents();
						examplesall.addComponent(examplestpizza);
						examplesall.addComponent(examplestvpizza);
					}
					if (current_ontology == "http://minerva.ual.es:8080/ontologies/course.owl") {
						examplesall.removeAllComponents();
						examplesall.addComponent(examplestcourse);
						examplesall.addComponent(examplestvcourse);
					}
					if (current_ontology == "http://minerva.ual.es:8080/ontologies/conference.owl") {
						examplesall.removeAllComponents();
						examplesall.addComponent(examplestconf);
						examplesall.addComponent(examplestvconf);
					}

				} catch (IOException e) {
					System.out.println(e.getMessage());
					error("Error Loading Ontology. Causes:", e.getMessage());
				}

			}

		});

		List<HashMap<String, RDFNode>> rows = new ArrayList<>();

		run_button.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {

				OntModel model = ModelFactory.createOntologyModel();
				model.read("file:C://working_ontology.owl");
				Query query = QueryFactory.create(editor.getValue());
				ResultSet result = (ResultSet) QueryExecutionFactory.create(query, model).execSelect();
				answers.removeAllColumns();
				List<String> variables = result.getResultVars();
				rows.clear();
				while (result.hasNext()) {
					QuerySolution solution = result.next();
					HashMap<String, RDFNode> sol = new HashMap<String, RDFNode>();
					for (String vari : variables) {
						sol.put(vari, solution.get(vari));
					}
					rows.add(sol);
				}
				answers.setItems(rows);
				if (rows.size() > 0) {
					answers.setVisible(true);
					HashMap<String, RDFNode> sr = rows.get(0);
					for (Map.Entry<String, RDFNode> entry : sr.entrySet()) {
						answers.addColumn(h -> h.get(entry.getKey())).setCaption(entry.getKey());
					}
				} else {
					error("Successful Execution", "Empty Answer of Query");
				}
			}
		});

		debug_button.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {
				result.setValue("");
				if (!debug.isVisible()) {
					debug.setVisible(true);
					debug_button.setCaption("Close Debug");
					answers.setVisible(false);
					result.setVisible(true);
					run_button.setVisible(false);
					ontologies.setEnabled(false);
					examplesall.setEnabled(false);
					new_ontology.setEnabled(false);
				} else {
					debug.setVisible(false);
					debug_button.setCaption("Debug Query");
					resP.setVisible(false);
					answers.setVisible(true);
					result.setVisible(false);
					run_button.setVisible(true);
					answers.setVisible(false);
					ontologies.setEnabled(true);
					examplesall.setEnabled(true);
					new_ontology.setEnabled(true);
				}
			}
		});

		correctness.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {

				manager = OWLManager.createOWLOntologyManager();
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/working_ontology.owl");
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontology. Causes:", e2.getMessage());
				}
				manager_owl = OWLManager.createOWLOntologyManager();
				df_owl = manager_owl.getOWLDataFactory();
				ont_owl = null;
				File file_owl = new File(owl);
				try {
					ont_owl = manager_owl.loadOntologyFromOntologyDocument(file_owl);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontology. Causes:", e2.getMessage());
				}

				manager_rdf = OWLManager.createOWLOntologyManager();
				df_rdf = manager_rdf.getOWLDataFactory();
				ont_rdf = null;
				File file_rdf = new File(rdf);
				try {
					ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontologgy. Causes:", e2.getMessage());
				}
				//BasicConfigurator.configure(new NullAppender());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				PrintStream ps = new PrintStream(baos);
				PrintStream old = System.out;
				System.setOut(ps);
				TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
						df_rdf, df_owl, "C:/working_ontology.owl");
				long startTime = System.currentTimeMillis();
				try {
					t.SPARQL_CORRECTNESS(editor.getValue());
				} catch (Exception e) {
					// TODO Auto-generated catch block
					error("Error Loading Query. Causes:", e.getMessage());
				}
				resP.setVisible(true);
				long estimatedTime = System.currentTimeMillis() - startTime;
				System.out.println("");
				System.out.println("<p>Analysis done in <b>" + estimatedTime + "</b> ms</p>");
				System.out.flush();
				System.setOut(old);
				result.setValue(baos.toString());
				System.out.println(baos.toString());
			}
		});

		type_validity.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {

				resP.setVisible(false);
				manager = OWLManager.createOWLOntologyManager();
				dataFactory = manager.getOWLDataFactory();
				ontology = null;
				File fileName = new File("C:/working_ontology.owl");
				try {
					ontology = manager.loadOntologyFromOntologyDocument(fileName);
				} catch (OWLOntologyCreationException e2) {
					System.out.println(e2.getMessage());
					error("Error Loading Ontology. Causes: ", e2.getMessage());
				}
				cb_type_validity.clear();
				cb_vars.clear();
				cb_type_validity.setVisible(true);
				cb_vars.setVisible(true);
				run_type_validity.setVisible(true);
				Set<OWLClass> classes_type_validity = ontology.getClassesInSignature();
				List<String> names = new ArrayList<String>();
				String urio = ontology.getOntologyID().getOntologyIRI().toString();
				int counter = 0;
				for (OWLClass c : classes_type_validity) {
					counter++;

					names.add(c.getIRI().toString());

				}
				cb_type_validity.setItems(names);
				cb_type_validity.setPageLength(counter);
				Query query = QueryFactory.create(editor.getValue());
				List<Var> vars = query.getProjectVars();
				cb_vars.setItems(vars);
				cb_vars.setPageLength(vars.size());
				type_validity.setEnabled(false);
				correctness.setEnabled(false);

			}
		});

		run_type_validity.addClickListener(new Button.ClickListener() {
			@Override
			public void buttonClick(ClickEvent event) {

				if (cb_type_validity.isEmpty() || cb_vars.isEmpty()) {
					error("", "Please select a class and an individual.");
				} else {
					manager_owl = OWLManager.createOWLOntologyManager();
					df_owl = manager_owl.getOWLDataFactory();
					ont_owl = null;
					File file_owl = new File(owl);
					try {
						ont_owl = manager_owl.loadOntologyFromOntologyDocument(file_owl);
					} catch (OWLOntologyCreationException e2) {
						System.out.println(e2.getMessage());
						error("Error Loading Ontology. Causes:", e2.getMessage());
					}
					manager_rdf = OWLManager.createOWLOntologyManager();
					df_rdf = manager_rdf.getOWLDataFactory();
					ont_rdf = null;
					File file_rdf = new File(rdf);
					try {
						ont_rdf = manager_rdf.loadOntologyFromOntologyDocument(file_rdf);
					} catch (OWLOntologyCreationException e2) {
						System.out.println(e2.getMessage());
						error("Error Loading Ontology. Causes:", e2.getMessage());
					}
					//org.apache.log4j.BasicConfigurator.configure(new NullAppender());
					ByteArrayOutputStream baos = new ByteArrayOutputStream();
					PrintStream ps = new PrintStream(baos);
					PrintStream old = System.out;
					System.setOut(ps);
					TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory,
							df_rdf, df_owl, "C:/working_ontology.owl");
					Optional<Var> variable_type_validity = cb_vars.getSelectedItem();
					Optional<String> type_type_validity = cb_type_validity.getSelectedItem();
					String var_name = variable_type_validity.get().getName().replace('?', ' ').replaceAll("\\s", "");
					String type_name = type_type_validity.get();
					long startTime = System.currentTimeMillis();
					try {
						t.SPARQL_TYPE_VALIDITY(editor.getValue(), var_name, type_name);
					} catch (Exception e) {
						// TODO Auto-generated catch block
						error("Error Loading Query", e.getMessage());
					}
					resP.setVisible(true);
					cb_type_validity.setVisible(false);
					cb_vars.setVisible(false);
					run_type_validity.setVisible(false);
					type_validity.setEnabled(true);
					correctness.setEnabled(true);
					long estimatedTime = System.currentTimeMillis() - startTime;
					System.out.println("");
					System.out.println("<p>Analysis done in <b>" + estimatedTime + "</b> ms</p>");
					System.out.flush();
					System.setOut(old);
					result.setValue(baos.toString());
				}
			}
		});

		edS.setContent(editor);
		resP.setContent(result);

		main.addComponent(lab);
		main.setWidth("100%");

		main.addComponent(ontologies);
		main.addComponent(new_ontology);
		main.addComponent(examplesall);
		main.addComponent(edS);
		main.addComponent(run_button);
		main.addComponent(debug_button);
		main.addComponent(answers);
		debug.addComponent(hlb);
		debug.addComponent(hlt);
		debug.addComponent(resP);
		main.addComponent(debug);

		Panel edO = new Panel("Loaded Ontology");
		edO.setSizeFull();
		edO.setContent(embedded);

		embedded.setHeight("800px");
		embedded.setWidth("100%");
	 

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

	public void error(String type, String message) {
		Notification notif = new Notification(type, message, Notification.Type.ERROR_MESSAGE);
		notif.setDelayMsec(20000);
		notif.setPosition(Position.BOTTOM_RIGHT);
		notif.show(Page.getCurrent());
	}

	@WebServlet(urlPatterns = "/*", name = "MyUIServlet", asyncSupported = true)
	@VaadinServletConfiguration(ui = MyUI.class, productionMode = false)
	public static class MyUIServlet extends VaadinServlet {
	}
}
