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
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Locale;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;

import javax.servlet.annotation.WebServlet;

import org.apache.log4j.varia.NullAppender;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDatatypeRestriction;
import org.semanticweb.owlapi.model.OWLFacetRestriction;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLRuntimeException;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.vaadin.aceeditor.AceEditor;
import org.vaadin.aceeditor.AceMode;
import org.vaadin.aceeditor.AceTheme;

import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import com.clarkparsia.owlapi.explanation.GlassBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;
import com.clarkparsia.owlapi.explanation.SingleExplanationGenerator;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import com.hp.hpl.jena.graph.Node;
import com.hp.hpl.jena.graph.NodeFactory;
import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFormatter;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.sparql.core.TriplePath;
import com.hp.hpl.jena.sparql.expr.Expr;
import com.hp.hpl.jena.sparql.expr.ExprFunctionOp;
import com.hp.hpl.jena.sparql.syntax.Element;
import com.hp.hpl.jena.sparql.syntax.ElementBind;
import com.hp.hpl.jena.sparql.syntax.ElementFilter;
import com.hp.hpl.jena.sparql.syntax.ElementGroup;
import com.hp.hpl.jena.sparql.syntax.ElementMinus;
import com.hp.hpl.jena.sparql.syntax.ElementOptional;
import com.hp.hpl.jena.sparql.syntax.ElementPathBlock;
import com.hp.hpl.jena.sparql.syntax.ElementSubQuery;
import com.hp.hpl.jena.sparql.syntax.ElementUnion;
import com.hp.hpl.jena.util.FileUtils;
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





/**
 * This UI is the application entry point. A UI may either represent a browser window 
 * (or tab) or some part of an HTML page where a Vaadin application is embedded.
 * <p>
 * The UI is initialized using {@link #init(VaadinRequest)}. This method is intended to be 
 * overridden to add component to the user interface and initialize non-component functionality.
 */
@Theme("mytheme")
public class MyUI3 extends UI {
	
	Integer next = 1;
	Integer current = 0;
	Integer nvar = 0;

	List<String> vars = new ArrayList<String>();
	List<List<String>> rules = new ArrayList<List<String>>();

	Map<String, Set<String>> domains_var = new HashMap<String, Set<String>>();
	Map<String, Set<String>> ranges_var = new HashMap<String, Set<String>>();
	Map<String, Set<String>> domains_predicate = new HashMap<String, Set<String>>();
	Map<String, Set<String>> ranges_predicate = new HashMap<String, Set<String>>();
	Set<String> vars_resources = new HashSet<String>();
	Set<String> vars_literals = new HashSet<String>();
	Set<TriplePath> ctriples = new HashSet<TriplePath>();
	Map<String, String> types_literals = new HashMap<String, String>();
	
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
	
	public String explanations(PelletReasonerFactory pfactory,Configuration configuration,
			OWLReasoner reasoner,GlassBoxExplanation exp,HSTExplanationGenerator multExplanator,OWLDataFactory dataFactory) {

		 

		String result = "";
		
		if (reasoner.isConsistent())
			result = "true";
		else {
		Set aboxAxiomsTypes = new HashSet();
		aboxAxiomsTypes.add(AxiomType.DATA_PROPERTY_ASSERTION);
		aboxAxiomsTypes.add(AxiomType.CLASS_ASSERTION);
		aboxAxiomsTypes.add(AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION);
		aboxAxiomsTypes.add(AxiomType.NEGATIVE_OBJECT_PROPERTY_ASSERTION);
		aboxAxiomsTypes.add(AxiomType.OBJECT_PROPERTY_ASSERTION);

		exp = new GlassBoxExplanation(ontology, pfactory);
		multExplanator = new HSTExplanationGenerator(exp);
		
		Set<Set<OWLAxiom>> explanations = multExplanator.getExplanations(dataFactory.getOWLThing());

		for (Set<OWLAxiom> explanation : explanations) {

			for (OWLAxiom causingAxiom : explanation) {
				if (!causingAxiom.isOfType(aboxAxiomsTypes))
					result = result + causingAxiom + "\n";

			}

		}
		}
		

		return result;
	}

	private String readFile(String pathname) throws IOException {

		File file = new File(pathname);
		StringBuilder fileContents = new StringBuilder((int) file.length());
		Scanner scanner = new Scanner(file);
		String lineSeparator = System.getProperty("line.separator");

		try {
			while (scanner.hasNextLine()) {
				fileContents.append(scanner.nextLine() + lineSeparator);
			}
			return fileContents.toString();
		} finally {
			scanner.close();
		}
	}

	public Boolean isClass(OWLOntology ont, String uri, String className) {

		if (ont.containsClassInSignature(IRI.create(uri + className)))
			return true;
		else
			return false;
	}

	public Boolean isDataProperty(OWLOntology ont, String uri, String className) {

		if (ont.containsDataPropertyInSignature(IRI.create(uri + className)))
			return true;
		else
			return false;
	}

	public Boolean isObjectProperty(OWLOntology ont, String uri, String className) {

		if (isDataProperty(ont, uri, className)) {
			return false;
		} else {

			if (ont.containsObjectPropertyInSignature(IRI.create(uri + className)))
				return true;
			else
				return false;
		}
	}

	public Boolean isIndividual(OWLOntology ont, String uri, String className) {

		if (ont.containsIndividualInSignature(IRI.create(uri + className)))
			return true;
		else
			return false;

	}

	public Boolean isObjectPropertyAll(String uri, String className) {
		return isObjectProperty(ontology, uri, className) || isObjectProperty(ont_rdf, uri, className)
				|| isObjectProperty(ont_owl, uri, className);
	}

	public Boolean isDataPropertyAll(String uri, String className) {
		return isDataProperty(ontology, uri, className) || isDataProperty(ont_rdf, uri, className)
				|| isDataProperty(ont_owl, uri, className);
	}

	public Boolean isIndividualAll(String uri, String className) {
		return isIndividual(ontology, uri, className) || isIndividual(ont_rdf, uri, className)
				|| isIndividual(ont_owl, uri, className);
	}

	public Boolean isClassAll(String uri, String className) {
		return isClass(ontology, uri, className) || isClass(ont_rdf, uri, className)
				|| isClass(ont_owl, uri, className);
	}

	public Boolean isDeclared(String uri, String className) {
		return isDataPropertyAll(uri, className) || isObjectPropertyAll(uri, className)
				|| isIndividualAll(uri, className) || isClassAll(uri, className);
	}

	public Set<String> RangesDataPropertyAll(IRI iri) {

		Set<String> s = new HashSet<String>();
		s.addAll(RangesDataProperty(ontology, dataFactory, iri));
		s.addAll(RangesDataProperty(ont_rdf, df_rdf, iri));
		s.addAll(RangesDataProperty(ont_owl, df_owl, iri));
		return s;

	}

	public Set<String> RangesObjectPropertyAll(IRI iri) {

		Set<String> s = new HashSet<String>();
		s.addAll(RangesObjectProperty(ontology, dataFactory, iri));
		s.addAll(RangesObjectProperty(ont_rdf, df_rdf, iri));
		s.addAll(RangesObjectProperty(ont_owl, df_owl, iri));
		return s;

	}

	public Set<String> DomainsDataPropertyAll(IRI iri) {

		Set<String> s = new HashSet<String>();
		s.addAll(DomainsDataProperty(ontology, dataFactory, iri));
		s.addAll(DomainsDataProperty(ont_rdf, df_rdf, iri));
		s.addAll(DomainsDataProperty(ont_owl, df_owl, iri));
		return s;

	}

	public Set<String> DomainsObjectPropertyAll(IRI iri) {

		Set<String> s = new HashSet<String>();
		s.addAll(DomainsObjectProperty(ontology, dataFactory, iri));
		s.addAll(DomainsObjectProperty(ont_rdf, df_rdf, iri));
		s.addAll(DomainsObjectProperty(ont_owl, df_owl, iri));
		return s;

	}

	public Set<String> RangesDataProperty(OWLOntology ont, OWLDataFactory df, IRI iri) {

		OWLDataProperty owlclass = df.getOWLDataProperty(iri);

		Set<OWLDataRange> ranges = owlclass.getRanges(ont);

		Set<String> result = new HashSet<String>();

		for (OWLDataRange range : ranges) {
			result.add(range.toString());
		}

		return result;
	}

	public Set<String> DomainsDataProperty(OWLOntology ont, OWLDataFactory df, IRI iri) {

		OWLDataProperty owlclass = df.getOWLDataProperty(iri);

		Set<OWLClassExpression> ranges = owlclass.getDomains(ont);

		Set<String> result = new HashSet<String>();

		for (OWLClassExpression range : ranges) {
			result.add(range.toString());
		}

		return result;
	}

	public Set<String> RangesObjectProperty(OWLOntology ont, OWLDataFactory df, IRI iri) {

		OWLObjectProperty owlclass = df.getOWLObjectProperty(iri);

		Set<OWLClassExpression> ranges = owlclass.getRanges(ont);

		Set<String> result = new HashSet<String>();

		for (OWLClassExpression range : ranges) {
			result.add(range.toString());
		}

		return result;
	}

	public Set<String> DomainsObjectProperty(OWLOntology ont, OWLDataFactory df, IRI iri) {

		OWLObjectProperty owlclass = df.getOWLObjectProperty(iri);

		Set<OWLClassExpression> ranges = owlclass.getDomains(ont);

		Set<String> result = new HashSet<String>();

		for (OWLClassExpression range : ranges) {
			result.add(range.toString());
		}

		return result;
	}

	public Set<OWLClass> ClassOfVariable(OWLOntology ont, OWLDataFactory df, IRI iri) {

		OWLNamedIndividual ni = df.getOWLNamedIndividual(iri);

		PelletReasonerFactory pellet = new PelletReasonerFactory();
		Configuration configuration = new Configuration();
		configuration.throwInconsistentOntologyException = false;
		OWLReasoner reas = pellet.createReasoner(ont, configuration);

		if (reas.isConsistent()) {

			NodeSet<OWLClass> classes = reas.getTypes(ni, true);
			Set<OWLClass> class_names = classes.getFlattened();
			return class_names;
		} else {

			return null;
		}

	}

	 

	public Set<OWLClassExpression> ClassOfVariable2(OWLOntology ont, OWLDataFactory df, IRI iri) {

		OWLNamedIndividual indi = df.getOWLNamedIndividual(iri);

		Set<OWLClassExpression> types = indi.getTypes(ont);

		Set<OWLClassExpression> result = new HashSet<OWLClassExpression>();

		for (OWLClassExpression type : types) {
			result.add(type);
		}

		return result;
	}

	public boolean isInteger(String s) {
		try {
			Integer.parseInt(s);
		} catch (NumberFormatException e) {
			return false;
		} catch (NullPointerException e) {
			return false;
		}

		return true;
	}

	public boolean isReal(String s) {
		try {
			Float.parseFloat(s);
		} catch (NumberFormatException e) {
			return false;
		} catch (NullPointerException e) {
			return false;
		}

		return true;
	}

	public boolean isBoolean(String s) {

		if ((s == "true") || (s == "false"))
			return true;
		else
			return false;
	}

	public Boolean isProperty(String Namespace) {
		if (Namespace == "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
			return false;
		else if (Namespace == "http://www.w3.org/2000/01/rdf-schema#")
			return false;
		else if (Namespace == "http://www.w3.org/2002/07/owl#")
			return false;
		else
			return true;
	};

	public String SPARQL(String filei, String queryStr) {

		OntModel model = ModelFactory.createOntologyModel();
		model.read(filei);
		com.hp.hpl.jena.query.Query query = QueryFactory.create(queryStr);

		if (query.isSelectType()) {
			ResultSet result = (ResultSet) QueryExecutionFactory.create(query, model).execSelect();
			File theDir = new File("tmp-sparql");
			if (!theDir.exists()) {
				theDir.mkdir();
			}
			String fileName = "./tmp-sparql/" + "result.owl";
			File f = new File(fileName);
			FileOutputStream file;
			try {
				file = new FileOutputStream(f);
				ResultSetFormatter.outputAsXML(file, (com.hp.hpl.jena.query.ResultSet) result);
				try {
					file.close();

				} catch (IOException e) {

					e.printStackTrace();
				}
			} catch (FileNotFoundException e1) {

				e1.printStackTrace();
			}

			String s = "";
			try {
				s = readFile(fileName);
			} catch (IOException e) {

				e.printStackTrace();
			}

			final File[] files = theDir.listFiles();
			for (File g : files)
				g.delete();
			theDir.delete();
			return s;
		} else

		if (query.isConstructType()) {
			Model result = QueryExecutionFactory.create(query, model).execConstruct();
			File theDir = new File("tmp-sparql");
			if (!theDir.exists()) {
				theDir.mkdir();
			}
			String fileName = "./tmp-sparql/" + "result.owl";
			File f = new File(fileName);
			FileOutputStream file;
			try {
				file = new FileOutputStream(f);
				result.write(file, FileUtils.langXMLAbbrev);
				try {
					file.close();

				} catch (IOException e) {

					e.printStackTrace();
				}
			} catch (FileNotFoundException e1) {

				e1.printStackTrace();
			}

			String s = "";
			try {
				s = readFile(fileName);
			} catch (IOException e) {

				e.printStackTrace();
			}
			final File[] files = theDir.listFiles();
			for (File g : files)
				g.delete();
			theDir.delete();
			return s;
		} else

		if (query.isDescribeType()) {
			Model result = QueryExecutionFactory.create(query, model).execDescribe();

			File theDir = new File("tmp-sparql");
			if (!theDir.exists()) {
				theDir.mkdir();
			}
			String fileName = "./tmp-sparql/" + "result.owl";

			File f = new File(fileName);

			FileOutputStream file;

			try {
				file = new FileOutputStream(f);
				result.write(file, FileUtils.langXMLAbbrev);
				try {
					file.close();

				} catch (IOException e) {

					e.printStackTrace();
				}
			} catch (FileNotFoundException e1) {

				e1.printStackTrace();
			}

			String s = "";
			try {
				s = readFile(fileName);
			} catch (IOException e) {

				e.printStackTrace();
			}
			final File[] files = theDir.listFiles();
			for (File g : files)
				g.delete();
			theDir.delete();
			return s;
		} else

		{
			Boolean b = QueryExecutionFactory.create(query, model).execAsk();
			return b.toString();
		}

	};

	public String ValueExpr(Expr e)

	{
		String arg = "";
		if (e.isVariable()) {

			arg = e.toString().replace('?', ' ').replaceAll("\\s", "");
			return arg;
		} else {
			if (e.isConstant()) {
				arg = e.toString();
				return arg;

			} else if (e.isFunction()) {
				List<Expr> exprs = e.getFunction().getArgs();
				if (!(exprs.size() == 2)) {
					return "wrong";
				} else
					return ValueExpr(e.getFunction().getArgs().get(0)) + e.getFunction().getOpName()
							+ ValueExpr(e.getFunction().getArgs().get(1));
			}
		}
		return "";
	}

	public String TypeExpr(Expr e, Map<String, Set<String>> types)

	{
		String arg = "";
		if (e.isVariable()) {

			arg = e.toString().replace('?', ' ').replaceAll("\\s", "");
			if (types.get(arg).contains("xsd:integer")) {
				return "integer";
			} else if (types.get(arg).contains("xsd:positiveInteger")) {
				return "integer";
			} else if (types.get(arg).contains("xsd:negativeInteger")) {
				return "integer";

			} else if (types.get(arg).contains("xsd:nonNegativeInteger")) {
				return "integer";

			} else if (types.get(arg).contains("xsd:nonPositiveInteger")) {
				return "integer";

			} else if (types.get(arg).contains("xsd:float")) {
				return "real";
			} else if (types.get(arg).contains("xsd:double")) {
				return "real";
			} else if (types.get(arg).contains("xsd:decimal")) {
				return "real";
			} else {
				return "wrong";
			}
		} else {
			if (e.isConstant()) {
				arg = e.toString();
				if (isInteger(arg)) {
					return "integer";
				} else if (isReal(arg)) {
					return "real";
				}

				else {
					return "wrong";
				}

			} else if (e.isFunction()) {
				List<Expr> exprs = e.getFunction().getArgs();
				if (!(exprs.size() == 2)) {
					return "wrong";
				} else {
					String type = "integer";
					for (Expr ex : exprs) {
						if (TypeExpr(ex, types) == "real") {
							type = "real";
						}
					}
					return type;
				}
			}
		}
		return "wrong";
	}

	public Stack<String> Restriction(OWLOntology ont, OWLClassExpression class_name, String nsproperty,
			String lnproperty, String var) {

		OWLClass owlclass = class_name.asOWLClass();

		Stack<String> constraint = new Stack<String>();

		for (OWLClassExpression c : owlclass.getEquivalentClasses(ont)) {

			if (c instanceof OWLDataSomeValuesFrom) {
				OWLDataSomeValuesFrom someValuesFrom = (OWLDataSomeValuesFrom) c;

				for (OWLDataProperty dp : c.getDataPropertiesInSignature()) {
					if (dp.getIRI().equals(IRI.create(nsproperty, lnproperty))) {

						OWLDataRange dataRange = someValuesFrom.getFiller();
						OWLDatatypeRestriction r = (OWLDatatypeRestriction) dataRange;

						if (r.getDatatype().isInteger()) {

							for (OWLFacetRestriction fr : r.getFacetRestrictions()) {

								if (fr.getFacet().toString() == "maxExclusive") {
									constraint.add(var.toUpperCase() + "#<" + fr.getFacetValue().getLiteral());
								} else if (fr.getFacet().toString() == "maxInclusive") {
									constraint.add(var.toUpperCase() + "#<=" + fr.getFacetValue().getLiteral());
								} else if (fr.getFacet().toString() == "minExclusive") {
									constraint.add(var.toUpperCase() + "#>" + fr.getFacetValue().getLiteral());
								} else if (fr.getFacet().toString() == "minInclusive") {
									constraint.add(var.toUpperCase() + "#>=" + fr.getFacetValue().getLiteral());
								}
							}
						}
					}

				}
			}
		}

		return constraint;
	}

	public Boolean Existence(TriplePath tp) {
		Boolean result = true;
		if (tp.getSubject().isURI() && !isDeclared(tp.getSubject().getNameSpace(), tp.getSubject().getLocalName())) {
			result = false;
		}

		if (tp.getPredicate().isURI()
				&& !isDeclared(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
			result = false;
		}

		if (tp.getObject().isURI() && !isDeclared(tp.getObject().getNameSpace(), tp.getObject().getLocalName())) {
			result = false;
		}

		return result;
	};

	public void Item_Analysis(ListIterator<TriplePath> it, OWLOntology ont, OWLDataFactory dft,
			OWLOntologyManager mng) {

		String urio = ont.getOntologyID().getOntologyIRI().toString();
		TriplePath tp = it.next();

		Boolean Existence = Existence(tp);

		if (Existence) {

			if (tp.getObject().isLiteral()) {
				if (tp.getPredicate().isURI()) {
					if (tp.getSubject().isLiteral()) /* LUL */ {
						System.out.println("Literal cannot be used as subject");
					} else if (tp.getSubject().isURI()) /* UUL */ {
						OWLNamedIndividual ni = dft.getOWLNamedIndividual(
								IRI.create(tp.getSubject().getNameSpace() + tp.getSubject().getLocalName()));

						if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
							OWLDataProperty o = dft.getOWLDataProperty(
									IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));

							OWLLiteral owlTypedLiteral = dft.getOWLLiteral(tp.getObject().getLiteralValue().toString(),
									dft.getOWLDatatype(IRI.create(tp.getObject().getLiteralDatatypeURI())));

							OWLAxiom axiom = dft.getOWLDataPropertyAssertionAxiom(o, ni, owlTypedLiteral);

							AddAxiom addAxiom = new AddAxiom(ont, axiom);

							mng.applyChange(addAxiom);

							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {

								e.printStackTrace();
							}

						} else
							System.out.println("Literal used with an object property or individual");
					} else /* VUL */

					{

						Set<String> ds = domains_var.get(tp.getSubject().getName().substring(0));
						if (ds == null) {
							ds = new HashSet<String>();
						}
						ds.add(tp.getPredicate().getURI());

						domains_var.put(tp.getSubject().getName().substring(0), ds);

						Set<String> dv = domains_predicate.get(tp.getPredicate().getURI());
						if (dv == null) {
							dv = new HashSet<String>();
						}
						dv.add(tp.getSubject().getName().substring(0));
						domains_predicate.put(tp.getPredicate().getURI(), dv);

						OWLNamedIndividual ni = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
							OWLDataProperty o = dft.getOWLDataProperty(
									IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));

							OWLLiteral owlTypedLiteral = dft.getOWLLiteral(tp.getObject().getLiteralValue().toString(),
									dft.getOWLDatatype(IRI.create(tp.getObject().getLiteralDatatypeURI())));

							OWLAxiom axiom = dft.getOWLDataPropertyAssertionAxiom(o, ni, owlTypedLiteral);

							AddAxiom addAxiom = new AddAxiom(ont, axiom);

							mng.applyChange(addAxiom);

							try {
								manager.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {

								e.printStackTrace();
							}
						} else
							System.out.println("Literal used with an object property or individual");

					}
				}

				else if (tp.getPredicate().isVariable()) {
					/* second V should be a data property */
					if (tp.getSubject().isVariable()) /* VVL */ {

						vars_resources.add(tp.getPredicate().getName().substring(0));
						vars_resources.add(tp.getSubject().getName().substring(0));

						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(
								IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
						OWLNamedIndividual ni2 = null;
						ni2 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
						OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls, ni2);
						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
						AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);

						mng.applyChange(addAxiom1);
						mng.applyChange(addAxiom2);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					} else if (tp.getSubject().isURI()) /* UVL */ {
						/* V should be a data property */
						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(
								IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));

						vars_resources.add(tp.getPredicate().getName().substring(0));
						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);

						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);

						mng.applyChange(addAxiom1);

						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					} else /* LVL */ {
						System.out.println("Literal cannot be used as subject");
					}
				} else /*-LL*/
					System.out.println("Literal cannot be used as property");
			}

			else if (tp.getObject().isURI()) {
				if (tp.getSubject().isLiteral()) /* L-U */ {
					System.out.println("Literal cannot be used as subject");
				} else {
					if (tp.getSubject().isVariable()) {
						if (tp.getPredicate().isLiteral()) /* VLU */ {
							System.out.println("Literal cannot be used as property");
						} else

						if (tp.getPredicate().isURI()) /* VUU */ {

							OWLNamedIndividual ni = null;
							ni = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(tp.getObject().getNameSpace() + tp.getObject().getLocalName()));

							Set<String> ds = domains_var.get(tp.getSubject().getName().substring(0));
							if (ds == null) {
								ds = new HashSet<String>();
							}
							ds.add(tp.getPredicate().getURI());

							domains_var.put(tp.getSubject().getName().substring(0), ds);

							Set<String> dv = domains_predicate.get(tp.getPredicate().getURI());
							if (dv == null) {
								dv = new HashSet<String>();
							}
							dv.add(tp.getSubject().getName().substring(0));
							domains_predicate.put(tp.getPredicate().getURI(), dv);

							if (isObjectPropertyAll(tp.getPredicate().getNameSpace(),
									tp.getPredicate().getLocalName())) {

								OWLObjectProperty o = dft.getOWLObjectProperty(IRI
										.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));

								OWLAxiom axiom = dft.getOWLObjectPropertyAssertionAxiom(o, ni, ni2);

								AddAxiom addAxiom = new AddAxiom(ont, axiom);

								mng.applyChange(addAxiom);

								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}

								OWLNamedIndividual ni1 = null;
								ni1 = dft.getOWLNamedIndividual(
										IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

								vars_resources.add(tp.getSubject().getName().substring(0));
								OWLClass cls = dft
										.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
								OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);

								AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);

								mng.applyChange(addAxiom1);

								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}

							} else
								System.out.println("Individual used with a data property or individual");

						} else { /* second V should be an object property */
							if (tp.getSubject().isVariable()) /* VVU */ {
								vars_resources.add(tp.getPredicate().getName().substring(0));
								vars_resources.add(tp.getSubject().getName().substring(0));
								OWLNamedIndividual ni1 = null;
								ni1 = dft.getOWLNamedIndividual(
										IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
								OWLNamedIndividual ni2 = null;
								ni2 = dft.getOWLNamedIndividual(
										IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
								OWLClass cls = dft
										.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
								OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
								OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls, ni2);
								AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
								AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);

								mng.applyChange(addAxiom1);
								mng.applyChange(addAxiom2);
								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}
							} else if (tp.getSubject().isURI()) /* UVU */ {
								/* V should be an object property */
								vars_resources.add(tp.getPredicate().getName().substring(0));
								OWLNamedIndividual ni1 = null;
								ni1 = dft.getOWLNamedIndividual(
										IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));

								OWLClass cls = dft
										.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
								OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);

								AddAxiom addAxiom1 = new AddAxiom(ontology, axiom1);

								mng.applyChange(addAxiom1);

								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}
							} else /* LVU */ {
								System.out.println("Literal cannot be used as subject");
							}
						}

					} else {
						if (tp.getPredicate().isLiteral()) /* ULU */
						{
							System.out.println("Literal cannot be a property");
						} else if (tp.getPredicate().isURI()) /* UUU */ {
							OWLNamedIndividual ni = null;
							ni = dft.getOWLNamedIndividual(
									IRI.create(tp.getSubject().getNameSpace() + tp.getSubject().getLocalName()));
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(tp.getObject().getNameSpace() + tp.getObject().getLocalName()));

							if (isObjectPropertyAll(tp.getPredicate().getNameSpace(),
									tp.getPredicate().getLocalName())) {
								OWLObjectProperty o = dft.getOWLObjectProperty(IRI
										.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));

								OWLAxiom axiom = dft.getOWLObjectPropertyAssertionAxiom(o, ni, ni2);

								AddAxiom addAxiom = new AddAxiom(ont, axiom);

								mng.applyChange(addAxiom);

								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}
							} else
								System.out.println("Individual used with a data property or individual");
						}

					}
				}
			}

			else

			if (tp.getSubject().isLiteral()) /* L-V */ {
				System.out.println("Literal cannot be used as subject");
			} else if (tp.getSubject().isVariable()) {

				if (tp.getPredicate().isLiteral()) /* VLV */
				{
					System.out.println("Literal cannot be a predicate");
				} else if (tp.getPredicate().isURI()) /* VUV */
				{
					// ADDING CONSTRAINED PROPERTY
					ctriples.add(tp);
					Set<String> ds = domains_var.get(tp.getSubject().getName().substring(0));
					if (ds == null) {
						ds = new HashSet<String>();
					}
					ds.add(tp.getPredicate().getURI());
					domains_var.put(tp.getSubject().getName().substring(0), ds);

					Set<String> dv = domains_predicate.get(tp.getPredicate().getURI());
					if (dv == null) {
						dv = new HashSet<String>();
					}
					dv.add(tp.getSubject().getName().substring(0));
					domains_predicate.put(tp.getPredicate().getURI(), dv);

					Set<String> dr = ranges_var.get(tp.getObject().getName().substring(0));
					if (dr == null) {
						dr = new HashSet<String>();
					}
					dr.add(tp.getPredicate().getURI());
					ranges_var.put(tp.getObject().getName().substring(0), dr);

					Set<String> rv = ranges_predicate.get(tp.getPredicate().getURI());
					if (rv == null) {
						rv = new HashSet<String>();
					}
					rv.add(tp.getObject().getName().substring(0));
					ranges_predicate.put(tp.getPredicate().getURI(), rv);

					if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
							&& !isObjectPropertyAll(tp.getPredicate().getNameSpace(),
									tp.getPredicate().getLocalName())) {

						vars_literals.add(tp.getObject().getName().substring(0));

						// ADD TYPE LITERAL
						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));

						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);

						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);

						mng.applyChange(addAxiom1);

						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						// ADD TYPE RANGE
						OWLNamedIndividual ni2 = null;
						ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
						for (String t : RangesDataPropertyAll(
								IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()))) {
							OWLClass cls2 = dft.getOWLClass(
									IRI.create("http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1)));

							OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls2, ni2);

							AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);

							mng.applyChange(addAxiom2);

							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
							types_literals.put(tp.getObject().getName().substring(0).toUpperCase(),
									"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
						}

					} else if (isObjectPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
							&& !isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
						OWLNamedIndividual ni1 = null;
						ni1 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						OWLNamedIndividual ni2 = null;
						ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));

						OWLObjectProperty o = dft.getOWLObjectProperty(
								IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));

						OWLAxiom axiom2 = dft.getOWLObjectPropertyAssertionAxiom(o, ni1, ni2);

						AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);

						mng.applyChange(addAxiom2);

						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}

					else {
					}

					vars_resources.add(tp.getSubject().getName().substring(0));
					OWLNamedIndividual ni1 = null;
					ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

					OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
					OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);

					AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);

					mng.applyChange(addAxiom1);

					try {
						mng.saveOntology(ont);
					} catch (OWLOntologyStorageException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}

				} else /* VVV */
				{
					vars_resources.add(tp.getPredicate().getName().substring(0));
					vars_resources.add(tp.getSubject().getName().substring(0));
					OWLNamedIndividual ni1 = null;
					ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
					OWLNamedIndividual ni2 = null;
					ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
					OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
					OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
					OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls, ni2);
					AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
					AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);

					mng.applyChange(addAxiom1);
					mng.applyChange(addAxiom2);
					try {
						mng.saveOntology(ont);
					} catch (OWLOntologyStorageException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}

			} else {

				if (tp.getPredicate().isLiteral()) /* ULV */ {
					System.out.println("Literal cannot be a predicate");
				} else if (tp.getPredicate().isURI()) /* UUV */
				{
					Set<String> dr = ranges_var.get(tp.getObject().getName().substring(0));
					if (dr == null) {
						dr = new HashSet<String>();
					}
					dr.add(tp.getPredicate().getURI());
					ranges_var.put(tp.getObject().getName().substring(0), dr);

					Set<String> rv = ranges_predicate.get(tp.getPredicate().getURI());
					if (rv == null) {
						rv = new HashSet<String>();
					}
					rv.add(tp.getObject().getName().substring(0));
					ranges_predicate.put(tp.getPredicate().getURI(), rv);

					if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
							&& !isObjectPropertyAll(tp.getPredicate().getNameSpace(),
									tp.getPredicate().getLocalName())) {
						vars_literals.add(tp.getObject().getName().substring(0));
						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));

						// ADD TYPE LITERAL
						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);

						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);

						mng.applyChange(addAxiom1);

						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						// ADD TYPE RANGE
						OWLNamedIndividual ni2 = null;
						ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
						for (String t : RangesDataPropertyAll(
								IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()))) {
							OWLClass cls2 = dft.getOWLClass(
									IRI.create("http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1)));

							OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls2, ni2);

							AddAxiom addAxiom2 = new AddAxiom(ontology, axiom2);

							mng.applyChange(addAxiom2);

							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
							types_literals.put(tp.getObject().getName().substring(0).toUpperCase(),
									"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
						}

					} else if (isObjectPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
							&& !isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(
								IRI.create(tp.getSubject().getNameSpace() + tp.getSubject().getLocalName()));
						OWLNamedIndividual ni2 = null;
						ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));

						OWLObjectProperty o = dft.getOWLObjectProperty(
								IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));

						//WHEN RDF:TYPE IS TREATED AS OBJECT PROPERTY
						OWLAxiom axiom2 = dft.getOWLObjectPropertyAssertionAxiom(o, ni1, ni2);

						AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);

						mng.applyChange(addAxiom2);

						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}

					else {
					}

				} else /* UVV */
				{
					vars_resources.add(tp.getPredicate().getName().substring(0));
					OWLNamedIndividual ni = null;
					ni = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));

					OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
					OWLAxiom axiom = dft.getOWLClassAssertionAxiom(cls, ni);

					AddAxiom addAxiom = new AddAxiom(ont, axiom);

					mng.applyChange(addAxiom);

					try {
						mng.saveOntology(ont);
					} catch (OWLOntologyStorageException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();

					}

				}
			}

		} else {
			System.out.println("There is some item not declared in the ontology\r\n");
		}
	};

	public List<List<String>> SPARQL_ANALYSIS(String file,String queryString, Integer step) {

		final Query query = QueryFactory.create(queryString);

		if (//query.hasValues() ||

				query.isConstructType() ||

				query.isDescribeType() ||

				query.isDistinct() ||

				query.hasAggregators() ||

				query.hasOrderBy() ||

				query.hasGroupBy() ||

				query.hasHaving() ||

				query.hasOffset() ||

				!query.getGraphURIs().isEmpty() ||

				!query.getNamedGraphURIs().isEmpty() ||

				query.hasLimit())

		{
			System.out.println("SPARQL expression not supported");

		}

		else

		{

			rules.add(current, new ArrayList());

			for (String v : query.getResultVars()) {
				vars.add(v.toUpperCase());
			}

			String head;

			if (vars.isEmpty()) {
				if (current == 0 && step == 0) {
					head = "p";
				} else {
					head = "p" + current + "_" + step;
				}

			} else {
				if (current == 0 && step == 0) {
					head = "p" + "(";
				} else {
					head = "p" + current + "_" + step + "(";
				}

				for (String v : vars) {
					head = head + v.toUpperCase() + ",";
				}

				head = head.substring(0, head.length() - 1);
				head = head + ")";
			}
			rules.get(current).add(0, head);

			Element e = query.getQueryPattern();

			

			elementGroup((ElementGroup) e, step, file);

			// CONSTRAINTS IN RDF

			String urio = ontology.getOntologyID().getOntologyIRI().toString();

			for (TriplePath tp : ctriples) {

				// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
				Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

				if (!(typ == null)) {

					// for (OWLClass c : typ) {
					for (OWLClassExpression c : typ) {
						Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
								tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

						List<String> ss = new ArrayList<>(s);
						for (int i = 0; i < ss.size(); i++) {

							rules.get(current).add(ss.get(i));
						}

					}
				}
			}
			ctriples.clear();
		}
		return rules;
	}

	public void elementFilter(ElementFilter el, Integer step, String fileo) {
		if (el.getExpr().getFunction().getFunctionName(null) == "exists") {

			List<String> varstemp = new ArrayList<String>();
			for (String v : vars) {
				varstemp.add(v);
			}

			Integer tmp = current;
			current = next;
			next++;
			rules.add(current, new ArrayList());

			Element ex = ((ExprFunctionOp) el.getExpr().getFunction()).getElement();
			if (ex instanceof ElementPathBlock) {
				elementPathBlock((ElementPathBlock) ex, step, fileo);

			} else if (ex instanceof ElementOptional) {
				elementOptional((ElementOptional) ex, step, fileo);
			} else if (ex instanceof ElementMinus) {
				elementMinus((ElementMinus) ex, step, fileo);
			} else if (ex instanceof ElementSubQuery) {
				elementSubQuery((ElementSubQuery) ex, step, fileo);
			} else if (ex instanceof ElementGroup) {
				elementGroup((ElementGroup) ex, step, fileo);
			} else if (ex instanceof ElementFilter) {
				elementFilter((ElementFilter) ex, step, fileo);
			} else if (ex instanceof ElementBind) {
				elementBind((ElementBind) ex, step, fileo);
			} else {
				System.out.println("SPARQL expression not supported");
				rules.clear();
			}

			// CONSTRAINTS IN RDF

			String urio = ontology.getOntologyID().getOntologyIRI().toString();

			for (TriplePath tp : ctriples) {

				// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
				Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

				if (!(typ == null)) {

					// for (OWLClass c : typ) {
					for (OWLClassExpression c : typ) {
						Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
								tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

						List<String> ss = new ArrayList<>(s);
						for (int i = 0; i < ss.size(); i++) {

							rules.get(current).add(ss.get(i));
						}

					}
				}
			}
			ctriples.clear();

			String head;

			if (vars.isEmpty()) {
				if (current == 0 && step == 0) {
					head = "p";
				} else {
					head = "p" + current + "_" + step;
				}

			} else {
				if (current == 0 && step == 0) {
					head = "p" + "(";
				} else {
					head = "p" + current + "_" + step + "(";
				}

				for (String v : vars) {
					head = head + v.toUpperCase() + ",";
				}
				head = head.substring(0, head.length() - 1);
				head = head + ")";
			}

			rules.get(current).add(0, head);
			rules.get(tmp).add(head);
			rules.get(current).add("!");

			for (String v : vars) {
				if (!varstemp.contains(v.toUpperCase())) {
					varstemp.add(v.toUpperCase());
				}
			}
			vars.clear();
			for (String v : varstemp) {
				vars.add(v);
			}
			current = tmp;

		} else

		if (el.getExpr().getFunction().getFunctionName(null) == "notexists") {

			List<String> varstemp = new ArrayList<String>();
			for (String v : vars) {
				varstemp.add(v);
			}

			Integer tmp = current;
			current = next;
			next++;
			rules.add(current, new ArrayList());

			Element ex = ((ExprFunctionOp) el.getExpr().getFunction()).getElement();
			if (ex instanceof ElementPathBlock) {
				elementPathBlock((ElementPathBlock) ex, step, fileo);

			} else if (ex instanceof ElementOptional) {
				elementOptional((ElementOptional) ex, step, fileo);
			} else if (ex instanceof ElementMinus) {
				elementMinus((ElementMinus) ex, step, fileo);
			} else if (ex instanceof ElementSubQuery) {
				elementSubQuery((ElementSubQuery) ex, step, fileo);
			} else if (ex instanceof ElementGroup) {
				elementGroup((ElementGroup) ex, step, fileo);
			} else if (ex instanceof ElementFilter) {
				elementFilter((ElementFilter) ex, step, fileo);
			} else if (ex instanceof ElementBind) {
				elementBind((ElementBind) ex, step, fileo);
			} else {
				System.out.println("SPARQL expression not supported");
				rules.clear();
			}

			String head;

			// CONSTRAINTS IN RDF
			String urio = ontology.getOntologyID().getOntologyIRI().toString();

			for (TriplePath tp : ctriples) {

				// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
				Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

				if (!(typ == null)) {

					// for (OWLClass c : typ) {
					for (OWLClassExpression c : typ) {
						Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
								tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

						List<String> ss = new ArrayList<>(s);
						for (int i = 0; i < ss.size(); i++) {

							rules.get(current).add(ss.get(i));
						}

					}
				}
			}
			ctriples.clear();

			if (vars.isEmpty()) {
				if (current == 0 && step == 0) {
					head = "p";
				} else {
					head = "p" + current + "_" + step;
				}

			} else {
				if (current == 0 && step == 0) {
					head = "p" + "(";
				} else {
					head = "p" + current + "_" + step + "(";
				}
				for (String v : vars) {
					head = head + v.toUpperCase() + ",";
				}
				head = head.substring(0, head.length() - 1);
				head = head + ")";
			}

			rules.get(current).add(0, head);
			rules.get(tmp).add("(\\+(" + head + "))");
			rules.get(current).add("!");

			for (String v : vars) {
				if (!varstemp.contains(v.toUpperCase())) {
					varstemp.add(v.toUpperCase());
				}
			}
			vars.clear();
			for (String v : varstemp) {
				vars.add(v);
			}
			current = tmp;

		} else if ((el.getExpr().getFunction().getOpName().toString() == "<")
				|| (el.getExpr().getFunction().getOpName().toString() == "<=")
				|| (el.getExpr().getFunction().getOpName().toString() == "=")
				|| (el.getExpr().getFunction().getOpName().toString() == ">")
				|| (el.getExpr().getFunction().getOpName().toString() == ">=")
				|| (el.getExpr().getFunction().getOpName().toString() == "!="))

		{
			nvar++;
			List<String> ss = new ArrayList<>(SExprtoPTerm(el.getExpr(), null));
			for (int i = 0; i < ss.size(); i++) {
				rules.get(current).add(ss.get(i));
			}

		}
	}

	public void elementBind(ElementBind el, Integer step, String fileo) {
		nvar++;
		List<String> ss = new ArrayList<>(SExprtoPTerm(el.getExpr(), el.getVar().asNode()));
		for (int i = 0; i < ss.size(); i++) {
			rules.get(current).add(ss.get(i));
		}
	}

	public void elementPathBlock(ElementPathBlock el, Integer step, String fileo) {

		List<TriplePath> lp = el.getPattern().getList();
		for (TriplePath p : lp) {

			if (!p.getSubject().isConcrete() && !vars.contains(STermtoPTerm(p.getSubject()))) {
				vars.add(STermtoPTerm(p.getSubject()));
			}
			if (!p.getPredicate().isConcrete() && !vars.contains(STermtoPTerm(p.getPredicate()))) {
				vars.add(STermtoPTerm(p.getPredicate()));
			}

			if (!p.getObject().isConcrete() && !vars.contains(STermtoPTerm(p.getObject()))) {
				vars.add(STermtoPTerm(p.getObject()));
			}

			ListIterator<TriplePath> it = el.getPattern().iterator();

			while (it.hasNext()) {

				Item_Analysis(it, ontology, dataFactory, manager);

			}

			/*
			 * String rule = "rdf(" + STermtoPTerm(p.getSubject()) + "," +
			 * STermtoPTerm(p.getPredicate()) + "," + STermtoPTerm(p.getObject()) + ")";
			 * List<String> l = rules.get(current); l.add(rule);
			 */

		}
	};

	public void elementUnion(ElementUnion el, Integer step, String fileo) {

		String union = "(";

		for (Element e : el.getElements()) {

			List<String> varstemp = new ArrayList<String>();
			for (String v : vars) {
				varstemp.add(v);
			}

			vars.clear();

			Integer tmp = current;
			current = next;
			next++;
			rules.add(current, new ArrayList());

			if (e instanceof ElementPathBlock) {
				elementPathBlock((ElementPathBlock) e, step, fileo);

			} else if (e instanceof ElementOptional) {
				elementOptional((ElementOptional) e, step, fileo);
			} else if (e instanceof ElementMinus) {
				elementMinus((ElementMinus) e, step, fileo);
			} else if (e instanceof ElementSubQuery) {
				elementSubQuery((ElementSubQuery) e, step, fileo);
			} else if (e instanceof ElementGroup) {
				elementGroup((ElementGroup) e, step, fileo);
			} else if (e instanceof ElementFilter) {
				elementFilter((ElementFilter) e, step, fileo);
			} else if (e instanceof ElementBind) {
				elementBind((ElementBind) e, step, fileo);
			} else if (e instanceof ElementUnion) {
				elementUnion((ElementUnion) e, step, fileo);
			} else {
				System.out.println("SPARQL expression not supported");
				rules.clear();
			}

			// CONSTRAINTS IN RDF

			String urio = ontology.getOntologyID().getOntologyIRI().toString();

			for (TriplePath tp : ctriples) {

				// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
				Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

				if (!(typ == null)) {

					// for (OWLClass c : typ) {
					for (OWLClassExpression c : typ) {
						Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
								tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

						List<String> ss = new ArrayList<>(s);
						for (int i = 0; i < ss.size(); i++) {

							rules.get(current).add(ss.get(i));
						}

					}
				}
			}
			ctriples.clear();

			String head;

			if (vars.isEmpty()) {
				if (current == 0 && step == 0) {
					head = "p";
				} else {
					head = "p" + current + "_" + step;
				}

			} else {
				if (current == 0 && step == 0) {
					head = "p" + "(";
				} else {
					head = "p" + current + "_" + step + "(";
				}
				for (String v : vars) {
					head = head + v.toUpperCase() + ",";
				}
				head = head.substring(0, head.length() - 1);
				head = head + ")";
			}

			rules.get(current).add(0, head);

			union = union + head + ";";

			for (String v : vars) {
				if (!varstemp.contains(v.toUpperCase())) {
					varstemp.add(v.toUpperCase());
				}
			}
			vars.clear();
			for (String v : varstemp) {
				vars.add(v);
			}
			current = tmp;
		}
		union = union.substring(0, union.length() - 1);
		union = union + ")";
		rules.get(current).add(union);

	}

	public void elementGroup(ElementGroup el, Integer step, String fileo) {

		for (Element e : el.getElements()) {

			if (e instanceof ElementPathBlock) {
				elementPathBlock((ElementPathBlock) e, step, fileo);
			} else if (e instanceof ElementOptional) {
				elementOptional((ElementOptional) e, step, fileo);
			} else if (e instanceof ElementMinus) {
				elementMinus((ElementMinus) e, step, fileo);
			} else if (e instanceof ElementSubQuery) {
				elementSubQuery((ElementSubQuery) e, step, fileo);
			} else if (e instanceof ElementUnion) {
				elementUnion((ElementUnion) e, step, fileo);
			} else if (e instanceof ElementFilter) {
				elementFilter((ElementFilter) e, step, fileo);
			} else if (e instanceof ElementBind) {
				elementBind((ElementBind) e, step, fileo);
			} else if (e instanceof ElementGroup) {
				elementGroup((ElementGroup) e, step, fileo);
			} else {
				System.out.println("SPARQL expression not supported");
				rules.clear();
			}

		}

	}

	public void elementMinus(ElementMinus el, Integer step, String fileo) {
		Element e = el.getMinusElement();

		List<String> varstemp = new ArrayList<String>();
		for (String v : vars) {
			varstemp.add(v);
		}

		Integer tmp = current;
		current = next;
		next++;
		rules.add(current, new ArrayList());

		if (e instanceof ElementPathBlock) {
			elementPathBlock((ElementPathBlock) e, step, fileo);

		} else if (e instanceof ElementOptional) {
			elementOptional((ElementOptional) e, step, fileo);
		} else if (e instanceof ElementMinus) {
			elementMinus((ElementMinus) e, step, fileo);
		} else if (e instanceof ElementSubQuery) {
			elementSubQuery((ElementSubQuery) e, step, fileo);
		} else if (e instanceof ElementGroup) {
			elementGroup((ElementGroup) e, step, fileo);
		} else if (e instanceof ElementFilter) {
			elementFilter((ElementFilter) e, step, fileo);
		} else if (e instanceof ElementBind) {
			elementBind((ElementBind) e, step, fileo);
		} else {
			System.out.println("SPARQL expression not supported");
			rules.clear();
		}

		// CONSTRAINTS IN RDF

		String urio = ontology.getOntologyID().getOntologyIRI().toString();

		for (TriplePath tp : ctriples) {

			// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
			Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

			if (!(typ == null)) {

				// for (OWLClass c : typ) {
				for (OWLClassExpression c : typ) {
					Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
							tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

					List<String> ss = new ArrayList<>(s);
					for (int i = 0; i < ss.size(); i++) {

						rules.get(current).add(ss.get(i));
					}

				}
			}
		}
		ctriples.clear();

		String head;

		if (vars.isEmpty()) {
			/* GOAL */
			if (current == 0 && step == 0) {
				head = "p";
			} else {
				head = "p" + current + "_" + step;
			}

		} else {
			/* GOAL */
			if (current == 0 && step == 0) {
				head = "p" + "(";
			} else {
				head = "p" + current + "_" + step + "(";
			}

			for (String v : vars) {
				head = head + v.toUpperCase() + ",";
			}
			head = head.substring(0, head.length() - 1);
			head = head + ")";
		}
		rules.get(current).add(0, head);
		rules.get(tmp).add("(\\+(" + head + "))");

		for (String v : vars) {
			if (!varstemp.contains(v.toUpperCase())) {
				varstemp.add(v.toUpperCase());
			}
		}
		vars.clear();
		for (String v : varstemp) {
			vars.add(v);
		}
		current = tmp;

	}

	public void elementOptional(ElementOptional el, Integer step, String fileo) {
		Element e = el.getOptionalElement();

		List<String> varstemp = new ArrayList<String>();
		for (String v : vars) {
			varstemp.add(v);
		}

		Integer tmp = current;
		current = next;
		next++;
		rules.add(current, new ArrayList());

		if (e instanceof ElementPathBlock) {
			elementPathBlock((ElementPathBlock) e, step, fileo);

		} else if (e instanceof ElementOptional) {
			elementOptional((ElementOptional) e, step, fileo);
		} else if (e instanceof ElementMinus) {
			elementMinus((ElementMinus) e, step, fileo);
		} else if (e instanceof ElementSubQuery) {
			elementSubQuery((ElementSubQuery) e, step, fileo);
		} else if (e instanceof ElementGroup) {
			elementGroup((ElementGroup) e, step, fileo);
		} else if (e instanceof ElementFilter) {
			elementFilter((ElementFilter) e, step, fileo);
		} else if (e instanceof ElementBind) {
			elementBind((ElementBind) e, step, fileo);
		} else {
			System.out.println("SPARQL expression not supported");
			rules.clear();
		}

		// CONSTRAINTS IN RDF

		String urio = ontology.getOntologyID().getOntologyIRI().toString();

		for (TriplePath tp : ctriples) {

			// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
			Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

			if (!(typ == null)) {

				// for (OWLClass c : typ) {
				for (OWLClassExpression c : typ) {
					Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
							tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

					List<String> ss = new ArrayList<>(s);
					for (int i = 0; i < ss.size(); i++) {

						rules.get(current).add(ss.get(i));
					}

				}
			}
		}
		ctriples.clear();
		//

		String head;

		if (vars.isEmpty()) {
			if (current == 0 && step == 0) {
				head = "p";
			} else {
				head = "p" + current + "_" + step;
			}

		} else {
			if (current == 0 && step == 0) {
				head = "p" + "(";
			} else {
				head = "p" + current + "_" + step + "(";
			}

			for (String v : vars) {
				head = head + v.toUpperCase() + ",";
			}
			head = head.substring(0, head.length() - 1);
			head = head + ")";
		}

		rules.get(current).add(0, head);
		rules.get(tmp).add("(" + head + ";" + "\\+(" + head + "))");

		for (String v : vars) {
			if (!varstemp.contains(v.toUpperCase())) {
				varstemp.add(v.toUpperCase());
			}
		}
		vars.clear();
		for (String v : varstemp) {
			vars.add(v);
		}
		current = tmp;

	};

	public void elementSubQuery(ElementSubQuery el, Integer step, String fileo) {

		Element e = el.getQuery().getQueryPattern();

		Query query = el.getQuery();

		if (query.hasValues() ||

				query.isConstructType() ||

				query.isDescribeType() ||

				query.isDistinct() ||

				query.hasAggregators() ||

				query.hasOrderBy() ||

				query.hasGroupBy() ||

				query.hasHaving() ||

				query.hasOffset() ||

				!query.getGraphURIs().isEmpty() ||

				!query.getNamedGraphURIs().isEmpty() ||

				query.hasLimit())

		{
			System.out.println("SPARQL expression not supported");

		}

		List<String> varstemp = new ArrayList<String>();
		for (String v : vars) {
			varstemp.add(v);
		}

		Integer tmp = current;
		current = next;
		next++;
		rules.add(current, new ArrayList());

		if (e instanceof ElementPathBlock) {
			elementPathBlock((ElementPathBlock) e, step, fileo);

		} else if (e instanceof ElementOptional) {
			elementOptional((ElementOptional) e, step, fileo);
		} else if (e instanceof ElementMinus) {
			elementMinus((ElementMinus) e, step, fileo);
		} else if (e instanceof ElementSubQuery) {
			elementSubQuery((ElementSubQuery) e, step, fileo);
		} else if (e instanceof ElementGroup) {
			elementGroup((ElementGroup) e, step, fileo);
		} else if (e instanceof ElementFilter) {
			elementFilter((ElementFilter) e, step, fileo);
		} else if (e instanceof ElementBind) {
			elementBind((ElementBind) e, step, fileo);
		} else {
			System.out.println("SPARQL expression not supported");
			rules.clear();
		}

		// CONSTRAINTS IN RDF

		String urio = ontology.getOntologyID().getOntologyIRI().toString();

		for (TriplePath tp : ctriples) {

			// Set<OWLClass> typ = ClassOfVariable(ontology,dataFactory,
			Set<OWLClassExpression> typ = ClassOfVariable2(ontology, dataFactory,
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

			if (!(typ == null)) {

				// for (OWLClass c : typ) {
				for (OWLClassExpression c : typ) {
					Stack<String> s = Restriction(ontology, c, tp.getPredicate().getNameSpace(),
							tp.getPredicate().getLocalName(), tp.getObject().getName().substring(0));

					List<String> ss = new ArrayList<>(s);
					for (int i = 0; i < ss.size(); i++) {

						rules.get(current).add(ss.get(i));
					}

				}
			}
		}
		ctriples.clear();

		String head;

		if (vars.isEmpty()) {
			if (current == 0 && step == 0) {
				head = "p";
			} else {
				head = "p" + current + "_" + step;
			}

		} else {
			if (current == 0 && step == 0) {
				head = "p" + "(";
			} else {
				head = "p" + current + "_" + step + "(";
			}

			for (String v : vars) {
				head = head + v.toUpperCase() + ",";
			}
			head = head.substring(0, head.length() - 1);
			head = head + ")";
		}

		rules.get(current).add(0, head);
		rules.get(tmp).add(head);

		for (String v : vars) {
			if (!varstemp.contains(v.toUpperCase())) {
				varstemp.add(v.toUpperCase());
			}
		}
		vars.clear();
		for (String v : varstemp) {
			vars.add(v);
		}

		current = tmp;

	}

	public String STermtoPTerm(Node st) {
		String pt = "";

		if (st.isVariable()) {
			if (st.getName().startsWith("?")) {
				pt = "X" + st.getName().substring(1);
			} else
				pt = st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase();

		} else if (st.isURI()) {
			pt = "'" + st.toString() + "'";
		}

		else if (st.isLiteral()) {
			if (st.getLiteralDatatypeURI() == null)

			{
				if (st.toString().startsWith("\"#")) {
					pt = st.toString().replaceAll("\"", "");
				} else {
					pt = st.toString() + "^^" + "'http://www.w3.org/2001/XMLSchema#string'";
				}
			}

			else {
				pt = st.getLiteralValue() + "^^'" + st.getLiteralDatatypeURI() + "'";
			}

		}

		return pt;
	}

	public Stack<String> SExprtoPTerm(Expr st, Node var) {
		Stack<String> pt = new Stack<String>();

		if (var == null) {
			if (st.isVariable()) {
				pt.add(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());

			} else if (st.isConstant()) {

				pt.add(st.toString() + "^^'" + st.getConstant().getDatatypeURI() + "'");

			}

			else if (st.isFunction()) {

				if (st.getFunction().getFunctionIRI() == null) {

					Integer act = nvar;
					nvar++;

					List<String> ss = new ArrayList<>(
							SExprtoPTerm(st.getFunction().getArg(1), NodeFactory.createVariable("A" + act)));

					for (int i = 0; i < ss.size(); i++) {
						pt.add(ss.get(i));
					}

					nvar++;
					List<String> ss2 = new ArrayList<>(
							SExprtoPTerm(st.getFunction().getArg(2), NodeFactory.createVariable("B" + act)));

					for (int i = 0; i < ss2.size(); i++) {
						pt.add(ss2.get(i));
					}

					if (types_literals.containsKey("A" + act)) {
						types_literals.put("B" + act,

								types_literals.get("A" + act));
					} else

					if (types_literals.containsKey("B" + act)) {
						types_literals.put("A" + act,

								types_literals.get("B" + act));
					}

					else
						System.out.println("Constraint are not enougly instantiated");

					if (types_literals.get("B" + act).equals("http://www.types.org#xsd:integer")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:string")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:dateTime")) {
						String Op = "";
						if (st.getFunction().getOpName().equals("!=")) {
							Op = "#\\=";
						} else if (st.getFunction().getOpName().equals("<=")) {
							Op = "#=<";
						} else {
							Op = "#" + st.getFunction().getOpName();
						}

						pt.add("A" + act + Op + "B" + act);
					} else
						if (types_literals.get("B" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
							String Op = "";
							if (st.getFunction().getOpName().equals("!=")) {
								Op = "#\\=";
							} else if (st.getFunction().getOpName().equals("<=")) {
								Op = "#=<";
							} else {
								Op = "#" + st.getFunction().getOpName();
							}

							pt.add("A" + act + Op + "B" + act);
							pt.add("B"+act+"#>=0");
						} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:positiveInteger")) {
							String Op = "";
							if (st.getFunction().getOpName().equals("!=")) {
								Op = "#\\=";
							} else if (st.getFunction().getOpName().equals("<=")) {
								Op = "#=<";
							} else {
								Op = "#" + st.getFunction().getOpName();
							}

							pt.add("A" + act + Op + "B" + act);
							pt.add("B"+act+"#>0");
						} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:negativeInteger")) {
							String Op = "";
							if (st.getFunction().getOpName().equals("!=")) {
								Op = "#\\=";
							} else if (st.getFunction().getOpName().equals("<=")) {
								Op = "#=<";
							} else {
								Op = "#" + st.getFunction().getOpName();
							}

							pt.add("A" + act + Op + "B" + act);
							pt.add("B"+act+"#<0");
						} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
							String Op = "";
							if (st.getFunction().getOpName().equals("!=")) {
								Op = "#\\=";
							} else if (st.getFunction().getOpName().equals("<=")) {
								Op = "#=<";
							} else {
								Op = "#" + st.getFunction().getOpName();
							}

							pt.add("A" + act + Op + "B" + act);
							pt.add("B"+act+"#=<0");
						} else
						
						if (types_literals.get("B" + act).equals("http://www.types.org#xsd:double")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:float")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:decimal")) {
						String Op = "";
						if (st.getFunction().getOpName().equals("!=")) {
							Op = "=\\=";
						} else if (st.getFunction().getOpName().equals("<=")) {
							Op = "=<";
						} else {
							Op = st.getFunction().getOpName();
						}
						pt.add("{" + "A" + act + Op + "B" + act + " }");

					} 
						
					 
					else
					{
					}

					nvar++;
				} else {

				}

			}
		} else

		if (st.isVariable()) {

			types_literals.put(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
					types_literals.get(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase()));

			if (types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:integer")
					|| types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:string")
					|| types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:dateTime")
					) {
				pt.add(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + "#="
						+ var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if (types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:positiveInteger")) {
				pt.add(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + "#="
						+ var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
				pt.add("0#<" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if (types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:negativeInteger")) {
				pt.add(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + "#="
						+ var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
				pt.add("0#>" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if (types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:nonNegativeInteger")) {
				pt.add(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + "#="
						+ var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
				pt.add("0#=<" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if (types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:nonPositivoInteger")) {
				pt.add(st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + "#="
						+ var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
				pt.add("0#>=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if (types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
					.equals("http://www.types.org#xsd:float")
					|| types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
							.equals("http://www.types.org#xsd:double")
					|| types_literals.get(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase())
							.equals("http://www.types.org#xsd:decimal")) {
				pt.add("{" + st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + "=:="
						+ var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase() + " }");
			} else {
			}

		} else if (st.isConstant()) {
			
			if (isValidFormat("dd/MM/yyyy", st.toString(), Locale.ENGLISH))
			{
				DateTimeFormatter fomatter = DateTimeFormatter.ofPattern("dd/MM/yyyy", Locale.ENGLISH);
				LocalDateTime ldt = LocalDateTime.parse(st.toString(), fomatter);
		        Integer result = ldt.hashCode();
		        
		        pt.add(result + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			}
			else
			if ((isInteger(st.toString()) || (isReal(st.toString())))) {
				
				pt.add(st.toString() + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
				
				}
			else {
				int MAX_LENGTH = 13;
				
				long result = 0;
				for (int i = 0; i < st.toString().length(); i++)
				   result += pow(27, MAX_LENGTH - i - 1)*(1 + st.toString().charAt(i));
				
				pt.add(result + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());	
			
			}

		}

		else if (st.isFunction()) {

			if (st.getFunction().getFunctionIRI() == null) {

				Integer act = nvar;
				nvar++;

				List<String> ss = new ArrayList<>(
						SExprtoPTerm(st.getFunction().getArg(1), NodeFactory.createVariable("A" + act)));

				for (int i = 0; i < ss.size(); i++)
					pt.add(ss.get(i));

				nvar++;
				List<String> ss2 = new ArrayList<>(
						SExprtoPTerm(st.getFunction().getArg(2), NodeFactory.createVariable("B" + act)));

				for (int i = 0; i < ss2.size(); i++)
					pt.add(ss2.get(i));

				types_literals.put("U" + act, types_literals.get("A" + act));
				types_literals.put("V" + act, types_literals.get("B" + act));

				if (types_literals.get("A" + act).equals("http://www.types.org#xsd:integer")
						|| types_literals.get("A" + act).equals("http://www.types.org#xsd:string") 
						|| types_literals.get("A" + act).equals("http://www.types.org#xsd:dateTime")) {
					pt.add("A" + act + " #= " + "U" + act);
				} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:positiveInteger")) {
					pt.add("A" + act + " #= " + "U" + act);
					pt.add("A" + act + " #> 0");
				} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:negativeInteger")) {
					pt.add("A" + act + " #= " + "U" + act);
					pt.add("A" + act + " #< 0");
				} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
					pt.add("A" + act + " #= " + "U" + act);
					pt.add("A" + act + " #>= 0");
				} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
					pt.add("A" + act + " #= " + "U" + act);
					pt.add("A" + act + " #=< 0");
				} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:float")
						|| types_literals.get("A" + act).equals("http://www.types.org#xsd:double")
						|| types_literals.get("A" + act).equals("http://www.types.org#xsd:decimal")) {
					pt.add("{" + "A" + act + " =:= " + "U" + act + " }");
				} else {
				}

				if (types_literals.get("B" + act).equals("http://www.types.org#xsd:integer")
						|| types_literals.get("B" + act).equals("http://www.types.org#xsd:string")
						|| types_literals.get("B" + act).equals("http://www.types.org#xsd:dateTime")) {
					pt.add("B" + act + " #= " + "V" + act);
				} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:positiveInteger")) {
					pt.add("B" + act + " #= " + "V" + act);
					pt.add("B" + act + " #> 0");
				} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:negativeInteger")) {
					pt.add("B" + act + " #= " + "V" + act);
					pt.add("B" + act + " #< 0");
				} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
					pt.add("B" + act + " #= " + "V" + act);
					pt.add("B" + act + " #>= 0");
				} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
					pt.add("B" + act + " #= " + "V" + act);
					pt.add("B" + act + " #=< 0");
				}

				else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:double")
						|| types_literals.get("B" + act).equals("http://www.types.org#xsd:float")
						|| types_literals.get("B" + act).equals("http://www.types.org#xsd:decimal")) {
					pt.add("{" + "B" + act + " =:= " + "V" + act + " }");
				} else {
				}

				types_literals.put("W" + act, types_literals.get("U" + act));

				if (types_literals.get("W" + act).equals("http://www.types.org#xsd:integer")
						|| types_literals.get("W" + act).equals("http://www.types.org#xsd:string")
						|| types_literals.get("W" + act).equals("http://www.types.org#xsd:dateTime")) {
					pt.add("W" + act + " #= " + "U" + act + st.getFunction().getOpName() + "V" + act);
				}

				else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:positiveInteger")) {
					pt.add("W" + act + " #= " + "U" + act + st.getFunction().getOpName() + "V" + act);
					pt.add("W" + act + " #> 0");
				} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:negativeInteger")) {
					pt.add("W" + act + " #= " + "U" + act + st.getFunction().getOpName() + "V" + act);
					pt.add("W" + act + " #< 0");
				} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
					pt.add("W" + act + " #= " + "U" + act + st.getFunction().getOpName() + "V" + act);
					pt.add("W" + act + " #>= 0");
				} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
					pt.add("W" + act + " #= " + "U" + act + st.getFunction().getOpName() + "V" + act);
					pt.add("W" + act + " #=< 0");
				} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:float")
						|| types_literals.get("W" + act).equals("http://www.types.org#xsd:double")
						|| types_literals.get("W" + act).equals("http://www.types.org#xsd:decimal"))

				{
					pt.add("{" + "W" + act + " =:= " + "U" + act + st.getFunction().getOpName() + "V" + act + "}");
				} else {
				}

				String res = var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase();

				types_literals.put(res, types_literals.get("W" + act));

				if (types_literals.get(res).equals("http://www.types.org#xsd:integer")
						|| types_literals.get(res).equals("http://www.types.org#xsd:string")
						|| types_literals.get(res).equals("http://www.types.org#xsd:dateTime")) {
					pt.add(res + " #=" + "W" + act);
				} else if (types_literals.get(res).equals("http://www.types.org#xsd:positiveInteger")) {
					pt.add(res + " #=" + "W" + act);
					pt.add(res + " #> 0");
				} else if (types_literals.get(res).equals("http://www.types.org#xsd:negativeInteger")) {
					pt.add(res + " #=" + "W" + act);
					pt.add(res + " #< 0");
				} else if (types_literals.get(res).equals("http://www.types.org#xsd:nonNegativeInteger")) {
					pt.add(res + " #=" + "W" + act);
					pt.add(res + " #>= 0");
				} else if (types_literals.get(res).equals("http://www.types.org#xsd:nonPositiveInteger")) {
					pt.add(res + " #=" + "W" + act);
					pt.add(res + " #=< 0");
				}

				else if (types_literals.get(res).equals("http://www.types.org#xsd:float")
						|| types_literals.get(res).equals("http://www.types.org#xsd:double")
						|| types_literals.get(res).equals("http://www.types.org#xsd:decimal")) {
					pt.add("{" + res + " =:=" + "W" + act + " }");
				} else {
				}

				nvar++;

			} else {

			}

		}

		return pt;
	}
	
	 
	public boolean isValidFormat(String format, String value, Locale locale) {
	    LocalDateTime ldt = null;
	    DateTimeFormatter fomatter = DateTimeFormatter.ofPattern(format, locale);

	    try {
	        ldt = LocalDateTime.parse(value, fomatter);
	        String result = ldt.format(fomatter);
	        return result.equals(value);
	    } catch (DateTimeParseException e) {
	        try {
	            LocalDate ld = LocalDate.parse(value, fomatter);
	            String result = ld.format(fomatter);
	            return result.equals(value);
	        } catch (DateTimeParseException exp) {
	            try {
	                LocalTime lt = LocalTime.parse(value, fomatter);
	                String result = lt.format(fomatter);
	                return result.equals(value);
	            } catch (DateTimeParseException e2) {
	               
	            }
	        }
	    }

	    return false;
	}
	
	public long pow(long a, int b)
	   {
	      if (b == 0)   return 1;
	      if (b == 1)   return a;
	      if (b%2 == 0) return   pow(a*a, b/2); //even a=(a^2)^b/2
	      else          return a*pow(a*a, b/2); //odd  a=a*(a^2)^b/2
	   }

	public void SPARQL_TYPING(String file,String query,OWLOntology ontology,PelletReasonerFactory pfactory,Configuration configuration,
			OWLReasoner reasoner,GlassBoxExplanation exp,HSTExplanationGenerator multExplanator,OWLDataFactory dataFactory) {
	 
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

		List<List<String>> rules = SPARQL_ANALYSIS(file,query, 0);
	
		String r = "";
		
		if (reasoner.isConsistent())
			r = "true";
		else {
			
			 GlassBoxExplanation.setup();
			     SingleExplanationGenerator eg = new GlassBoxExplanation(ontology,
			              PelletReasonerFactory.getInstance());
			      try {
			          for (OWLAxiom ax : eg.getExplanation(dataFactory.getOWLThing())) {
			        	  r = r + ax + "\n";
			          }
			      } catch (OWLRuntimeException ex) {
			          System.out.println("cannot explain: " + ex.getMessage());
			      }
			 
		/*try {
			
			Set aboxAxiomsTypes = new HashSet();
			aboxAxiomsTypes.add(AxiomType.DATA_PROPERTY_ASSERTION);
			aboxAxiomsTypes.add(AxiomType.CLASS_ASSERTION);
			aboxAxiomsTypes.add(AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION);
			aboxAxiomsTypes.add(AxiomType.NEGATIVE_OBJECT_PROPERTY_ASSERTION);
			aboxAxiomsTypes.add(AxiomType.OBJECT_PROPERTY_ASSERTION);

			exp = new GlassBoxExplanation(ontology, pfactory);
			multExplanator = new HSTExplanationGenerator(exp);
			
			Set<Set<OWLAxiom>> explanations = multExplanator.getExplanations(dataFactory.getOWLThing());

			for (Set<OWLAxiom> explanation : explanations) {

				for (OWLAxiom causingAxiom : explanation) {
					if (!causingAxiom.isOfType(aboxAxiomsTypes))
						r = r + causingAxiom + "\n";

				}

			}
			
			
			//r = explanations(pfactory,configuration,reasoner,exp,multExplanator,dataFactory);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}*/
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

	
	public void SPARQL_CHECKING(String file,String query) {

		 
		List<List<String>> rules = SPARQL_ANALYSIS(file,query, 0);

		

		String t1 = "use_module(library('clpfd'))";
		org.jpl7.Query q1 = new org.jpl7.Query(t1);
		System.out.print((q1.hasSolution() ? "" : ""));
		String t2 = "use_module(library('clpq'))";
		org.jpl7.Query q2 = new org.jpl7.Query(t2);
		System.out.print((q2.hasSolution() ? "" : ""));

		for (List<String> rule : rules) {
			String c = "";
			if (rule.size() >= 2) {
				c = rule.get(0) + ":-";
				for (int i = 1; i < rule.size(); i++) {
					c = c + rule.get(i) + ',';
				}
				c = c.substring(0, c.length() - 1);
			} else {
				c = rule.get(0);
			}

			//DELETE PREVIOUS RULES
			String dr = rule.get(0);
			org.jpl7.Query drq = new org.jpl7.Query("retractall(" + dr + ")");
			System.out.print((drq.hasSolution() ? "" : ""));
			
			//System.out.println(c);
			String aprule = "asserta((" + c + "))";
			org.jpl7.Query q4 = new org.jpl7.Query(aprule);
			System.out.print((q4.hasSolution() ? "" : ""));
			
		}
		
		org.jpl7.Query q4 = new org.jpl7.Query(rules.get(0).get(0));

		if (!q4.hasSolution()) {
			System.out.println("Unsuccessful Checking");
		} else

		{
			System.out.println("Successful Checking");
		}
	}

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

		pfactory = new PelletReasonerFactory();
		configuration = new Configuration();
		configuration.throwInconsistentOntologyException = false;
		reasoner = pfactory.createReasoner(ontology, configuration);
		 
		
		final VerticalLayout layout = new VerticalLayout();

		Label lab = new Label("TSPARQL: Typing, Consistency Checking and Testing of SPARQL");
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
		
				result.setValue("");
				
				SPARQL_TYPING(filet.getValue(),editor.getValue(),ontology,pfactory,configuration,
						reasoner,exp,multExplanator,dataFactory);
				
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
		
				SPARQL_CHECKING(filet.getValue(),editor.getValue());
				
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
	
	
	
    @WebServlet(urlPatterns = "/*", name = "MyUIServlet", asyncSupported = true)
    @VaadinServletConfiguration(ui = MyUI3.class, productionMode = false)
    public static class MyUIServlet extends VaadinServlet {
    }
}
