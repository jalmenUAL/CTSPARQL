package CTSPARQL;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
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

import org.apache.jena.graph.Node;
import org.apache.jena.graph.NodeFactory;
import org.apache.jena.ontology.OntModel;
import org.apache.jena.query.Query;
import org.apache.jena.query.QueryExecutionFactory;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.ResultSet;
import org.apache.jena.query.ResultSetFormatter;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.sparql.core.TriplePath;
import org.apache.jena.sparql.expr.Expr;
import org.apache.jena.sparql.syntax.Element;
import org.apache.jena.sparql.syntax.ElementBind;
import org.apache.jena.sparql.syntax.ElementFilter;
import org.apache.jena.sparql.syntax.ElementGroup;
import org.apache.jena.sparql.syntax.ElementMinus;
import org.apache.jena.sparql.syntax.ElementOptional;
import org.apache.jena.sparql.syntax.ElementPathBlock;
import org.apache.jena.sparql.syntax.ElementSubQuery;
import org.apache.jena.sparql.syntax.ElementUnion;
import org.apache.jena.util.FileUtils;
import org.jpl7.Term;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDatatypeRestriction;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLFacetRestriction;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLRuntimeException;
import org.semanticweb.owlapi.model.RemoveAxiom;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import com.clarkparsia.owlapi.explanation.GlassBoxExplanation;
import com.clarkparsia.owlapi.explanation.SingleExplanationGenerator;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;

import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;

public class TSPARQL {

	Boolean show = true;
	Boolean negation = false;
	Integer next = 1;
	Integer current = 0;
	Integer nvar = 0;
	Boolean error = false;
	List<String> vars = new ArrayList<String>();
	List<List<String>> rules = new ArrayList<List<String>>();
	Set<TriplePath> ctriples = new HashSet<TriplePath>();
	Map<Node, Map<Node, Set<Node>>> ctriplesn = new HashMap<Node, Map<Node, Set<Node>>>();
	Map<String, String> types_literals = new HashMap<String, String>();
	Set<String> constraints_elements = new HashSet<String>();
	Set<TriplePath> datatriples = new HashSet<TriplePath>();
	Map<String, String> rename = new HashMap<String, String>();
	OWLOntologyManager manager;
	OWLOntologyManager manager_rdf;
	OWLOntologyManager manager_owl;
	OWLOntology ontology;
	OWLOntology ont_rdf;
	OWLOntology ont_owl;
	OWLDataFactory dataFactory;
	OWLDataFactory df_rdf;
	OWLDataFactory df_owl;
	Boolean wrong_analysis = false;
	String file;

	public TSPARQL(OWLOntologyManager manager, OWLOntologyManager manager_rdf, OWLOntologyManager manager_owl,
			OWLOntology ontology, OWLOntology ont_rdf, OWLOntology ont_owl, OWLDataFactory dataFactory,
			OWLDataFactory df_rdf, OWLDataFactory df_owl, String file) {

		this.rename.clear();
		this.constraints_elements.clear();
		this.vars.clear();
		this.ctriples.clear();
		this.ctriplesn.clear();
		this.datatriples.clear();
		this.types_literals.clear();
		this.rules.clear();
		this.manager = manager;
		this.manager_rdf = manager_rdf;
		this.manager_owl = manager_owl;
		this.ontology = ontology;
		this.ont_rdf = ont_rdf;
		this.ont_owl = ont_owl;
		this.dataFactory = dataFactory;
		this.df_rdf = df_rdf;
		this.df_owl = df_owl;
		this.wrong_analysis = false;
		this.file = file;

	}

	public String sparql_constraint_checking() {

		String result = "";
		String t1 = "use_module(library('clpfd'))";
		org.jpl7.Query q1 = new org.jpl7.Query(t1);
		System.out.print((q1.hasSolution() ? "" : ""));
		String t2 = "use_module(library('clpr'))";
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
			String dr = rule.get(0);
			org.jpl7.Query drq = new org.jpl7.Query("retractall(" + dr + ")");
			System.out.print((drq.hasSolution() ? "" : ""));
			String aprule = "asserta((" + c + "))";
			org.jpl7.Query q3 = new org.jpl7.Query(aprule);
			System.out.print((q3.hasSolution() ? "" : ""));
		}

		org.jpl7.Query q4 = new org.jpl7.Query(rules.get(0).get(0));
		if (!q4.hasSolution()) {
			for (String c : constraints_elements) {
				result = result + c.replace("?", "") + " ";
			}
		} else {
			result = "true";
		}

		return result;
	}

	public String sparql_consistency() {
		String result = "";
		File fileName = new File(file);
		manager.removeOntology(ontology);
		try {
			ontology = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {

			System.out.println(e2.getMessage());
		}

		PelletReasonerFactory f = new PelletReasonerFactory();
		OWLReasoner reasoner = f.createReasoner(ontology);
		ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		if (reasoner.isConsistent()) {
			result = "true";
			reasoner.dispose();
		} else {
			GlassBoxExplanation.setup();
			SingleExplanationGenerator eg = new GlassBoxExplanation(ontology, f);
			try {
				for (OWLAxiom ax : eg.getExplanation(dataFactory.getOWLThing())) {
					result = result + "<p style=\"color:blue\">" + rendering.render(ax) + "</p>";
				}
			} catch (OWLRuntimeException ex) {
				System.out.println("<p style=\"color:blue\"> cannot explain: " + ex.getMessage() + "</p>");
			}
			reasoner.dispose();
		}
		return result;
	}

	public String explanations() {
		String result = "";
		File fileName = new File(file);
		manager.removeOntology(ontology);
		try {
			ontology = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {

			System.out.println(e2.getMessage());
		}
		ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		PelletReasonerFactory f = new PelletReasonerFactory();
		OWLReasoner reasoner = f.createReasoner(ontology);
		GlassBoxExplanation.setup();
		SingleExplanationGenerator eg = new GlassBoxExplanation(ontology, f);
		try {
			for (OWLAxiom ax : eg.getExplanation(dataFactory.getOWLThing())) {
				result = result + "<p style=\"color:blue\">" + rendering.render(ax) + "</p>";
			}
		} catch (OWLRuntimeException ex) {
			System.out.println("<p style=\"color:blue\">" + "cannot explain: " + ex.getMessage() + "</p>");
		}
		reasoner.dispose();
		return result;
	}

	public String consistency() {
		String result = "";
		File fileName = new File(file);
		manager.removeOntology(ontology);
		try {
			ontology = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {
			System.out.println(e2.getMessage());
		}
		PelletReasonerFactory f = new PelletReasonerFactory();
		OWLReasoner reasoner = f.createReasoner(ontology);
		if (reasoner.isConsistent()) {
			result = "true";
			reasoner.dispose();
		} else {
			result = "false";
			reasoner.dispose();
		}
		return result;
	}

	public String entailment(OWLAxiom ax) {
		String result = "";
		File fileName = new File(file);
		manager.removeOntology(ontology);
		try {
			ontology = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {
			System.out.println(e2.getMessage());
		}
		PelletReasonerFactory f = new PelletReasonerFactory();
		OWLReasoner reasoner = f.createReasoner(ontology);
		if (reasoner.isConsistent()) {
			if (reasoner.isEntailed(ax)) {
				result = "true";
			} else {
				result = "false";
			}
			reasoner.dispose();
		} else {
			System.out.println("<p style=\"color:Tomato;\">Inconsistent query, please check consistency</p>");
			wrong_analysis = true;
		}
		return result;
	}

	private void printClass(Object class_name, Object individual_name) {
		System.out.println("<p style=\"color:blue\">" + individual_name + " Type " + class_name + "</p>");
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
		result.add(df.getOWLThing().toString());
		return result;
	}

	public Set<OWLClassExpression> ClassOfVariable(IRI iri) {
		File fileName = new File(file);
		manager.removeOntology(ontology);
		try {
			ontology = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {

			System.out.println(e2.getMessage());
		}
		OWLNamedIndividual indi = dataFactory.getOWLNamedIndividual(iri);
		Set<OWLClassExpression> types = indi.getTypes(ontology);
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
		Query query = QueryFactory.create(queryStr);
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
				ResultSetFormatter.outputAsXML(file, (ResultSet) result);
				try {
					file.close();
				} catch (IOException e) {

					System.out.println(e.getMessage());
				}
			} catch (FileNotFoundException e1) {

				System.out.println(e1.getMessage());
			}

			String s = "";
			try {
				s = readFile(fileName);
			} catch (IOException e) {

				System.out.println(e.getMessage());
			}

			final File[] files = theDir.listFiles();
			for (File g : files)
				g.delete();
			theDir.delete();
			return s;
		} else if (query.isConstructType()) {
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

					System.out.println(e.getMessage());
				}
			} catch (FileNotFoundException e1) {

				System.out.println(e1.getMessage());
			}
			String s = "";
			try {
				s = readFile(fileName);
			} catch (IOException e) {

				System.out.println(e.getMessage());
			}
			final File[] files = theDir.listFiles();
			for (File g : files)
				g.delete();
			theDir.delete();
			return s;
		} else if (query.isDescribeType()) {
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

					System.out.println(e.getMessage());
				}
			} catch (FileNotFoundException e1) {
				System.out.println(e1.getMessage());
			}
			String s = "";
			try {
				s = readFile(fileName);
			} catch (IOException e) {

				System.out.println(e.getMessage());
			}
			final File[] files = theDir.listFiles();
			for (File g : files)
				g.delete();
			theDir.delete();
			return s;
		} else {
			Boolean b = QueryExecutionFactory.create(query, model).execAsk();
			return b.toString();
		}
	};

	public String ValueExpr(Expr e) {
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
				} else {
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

	public String print(TriplePath tp) {
		return "<pre>" + tp.getSubject() + " " + tp.getPredicate().getLocalName() + " " + tp.getObject() + "</pre>";

	}

	public Boolean Existence(TriplePath tp) {
		Boolean result = true;
		if (tp.getSubject().isURI() && !isDeclared(tp.getSubject().getNameSpace(), tp.getSubject().getLocalName())
				&& !wrong_analysis) {
			System.out.print("<p style=\"color:green\">" + "This item is not declared by the ontology: " + "</p>");
			System.out.println("<p>" + tp.getSubject().getLocalName() + "</p>");
			System.out.println("<p> Triple: " + print(tp) + "</p>");
			result = false;
			wrong_analysis = true;
		}
		if (tp.getPredicate().isURI() && !isDeclared(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
				&& !wrong_analysis) {
			System.out.print("<p style=\"color:green\">" + "This item is not declared by the ontology: " + "</p>");
			System.out.println("<p>" + tp.getPredicate().getLocalName() + "</p>");
			System.out.println("<p> Triple: " + print(tp) + "</p>");
			result = false;
			wrong_analysis = true;
		}
		if (tp.getObject().isURI() && !isDeclared(tp.getObject().getNameSpace(), tp.getObject().getLocalName())
				&& !wrong_analysis) {
			System.out.print("<p style=\"color:green\">" + "This item is not declared by the ontology: " + "</p>");
			System.out.println("<p>" + tp.getObject().getLocalName() + "</p>");
			System.out.println("<p> Triple: " + print(tp) + "</p>");
			result = false;
			wrong_analysis = true;
		}
		return result;
	};

	public void Item_Analysis(ListIterator<TriplePath> it, OWLOntology ont, OWLDataFactory dft,
			OWLOntologyManager mng) {

		String urio = ont.getOntologyID().getOntologyIRI().toString();
		TriplePath tp = it.next();

		Boolean linear = true;
		if (ctriplesn.containsKey(tp.getSubject())) {
			if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {
				if (!ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).contains(tp.getObject())) {
					linear = false;
				}
			}
		}

		if (linear) {

			Boolean Existence = Existence(tp);
			if (Existence) {
				if (tp.getObject().isLiteral()) {
					if (tp.getPredicate().isURI()) {
						if (tp.getSubject().isLiteral()) /* LUL */ {
							System.out.println(
									"<p style=\"color:green\">" + "Literal cannot be used as subject:" + "</p>");
							System.out.println("<p> Triple: " + print(tp) + "</p>");
							wrong_analysis = true;
						} else if (tp.getSubject().isURI()) /* UUL */ {

							// STORE TRIPLE PATTERN
							ctriples.add(tp);
							if (ctriplesn.containsKey(tp.getSubject())) {
								if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {
									ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
								}
							} else {
								Set<Node> content = new HashSet<Node>();
								content.add(tp.getObject());
								Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
								map.put(tp.getPredicate(), content);
								ctriplesn.put(tp.getSubject(), map);
							}

							// ADD TRIPLE PATTERN
							OWLNamedIndividual ni = dft.getOWLNamedIndividual(
									IRI.create(tp.getSubject().getNameSpace() + tp.getSubject().getLocalName()));
							if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
								OWLDataProperty o = dft.getOWLDataProperty(IRI
										.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
								OWLLiteral owlTypedLiteral = dft.getOWLLiteral(
										tp.getObject().getLiteralValue().toString(),
										dft.getOWLDatatype(IRI.create(tp.getObject().getLiteralDatatypeURI())));
								OWLAxiom axiom = dft.getOWLDataPropertyAssertionAxiom(o, ni, owlTypedLiteral);
								AddAxiom addAxiom = new AddAxiom(ont, axiom);
								mng.applyChange(addAxiom);
								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									System.out.println(e.getMessage());
								}
							} else {
								System.out.println(
										"<p style=\"color:green\">" + "Literal used with an object property:" + "</p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
								wrong_analysis = true;
							}
						} else /* VUL */
						{

							// ADD TYPE
							OWLNamedIndividual ni = null;
							ni = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
							OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom = dft.getOWLClassAssertionAxiom(cls, ni);
							AddAxiom addAxiom = new AddAxiom(ont, axiom);
							mng.applyChange(addAxiom);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}
							// STORE TRIPLE PATTERN
							ctriples.add(tp);
							if (ctriplesn.containsKey(tp.getSubject())) {
								if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {

									ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());

								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
								}
							} else {
								Set<Node> content = new HashSet<Node>();
								content.add(tp.getObject());
								Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
								map.put(tp.getPredicate(), content);
								ctriplesn.put(tp.getSubject(), map);
							}

							// ADD TRIPLE PATTERN
							OWLNamedIndividual ni2 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
							if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
								OWLDataProperty o = dft.getOWLDataProperty(IRI
										.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
								OWLLiteral owlTypedLiteral = dft.getOWLLiteral(
										tp.getObject().getLiteralValue().toString(),
										dft.getOWLDatatype(IRI.create(tp.getObject().getLiteralDatatypeURI())));
								OWLAxiom axiom2 = dft.getOWLDataPropertyAssertionAxiom(o, ni2, owlTypedLiteral);
								AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);
								mng.applyChange(addAxiom2);
								try {
									manager.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									System.out.println(e.getMessage());
								}
							} else {
								System.out.println(
										"<p style=\"color:green\">" + "Literal used with an object property:" + "<p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
								wrong_analysis = true;
							}
						}
					} else if (tp.getPredicate().isVariable()) {
						/* second V should be a data property */
						if (tp.getSubject().isVariable()) /* VVL */ {

							// ADD TYPE
							OWLNamedIndividual ni1 = null;
							ni1 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
							OWLClass cls1 = dft
									.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls1, ni1);
							AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
							mng.applyChange(addAxiom1);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
							OWLClass cls2 = dft
									.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls2, ni2);
							AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);
							mng.applyChange(addAxiom2);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}

						} else if (tp.getSubject().isURI()) /* UVL */ {
							/* V should be a data property */

							// ADD TYPE
							OWLNamedIndividual ni1 = null;
							ni1 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
							OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
							AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
							mng.applyChange(addAxiom1);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}
						} else /* LVL */ {
							{
								System.out.println(
										"<p style=\"color:green\">" + "Literal cannot be used as subject:" + "</p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
								wrong_analysis = true;
							}
						}
					} else /*-LL*/
					{
						System.out
								.println("<p style=\"color:green\">" + "Literal cannot be used as property:" + "</p>");
						System.out.println("<p> Triple: " + print(tp) + "</p>");
						wrong_analysis = true;
					}
				} else if (tp.getObject().isURI()) {
					if (tp.getSubject().isLiteral()) /* L-U */ {
						System.out.println("<p style=\"color:green\">" + "Literal cannot be used as subject:" + "</p>");
						System.out.println("<p> Triple: " + print(tp) + "</p>");
						wrong_analysis = true;
					} else {
						if (tp.getSubject().isVariable()) {
							if (tp.getPredicate().isLiteral()) /* VLU */ {
								System.out.println(
										"<p style=\"color:green\">" + "Literal cannot be used as property:" + "</p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
								wrong_analysis = true;
							} else if (tp.getPredicate().isURI()) /* VUU */ {

								if (isObjectPropertyAll(tp.getPredicate().getNameSpace(),
										tp.getPredicate().getLocalName())) {

									// ADD TYPE
									OWLNamedIndividual ni1 = null;
									ni1 = dft.getOWLNamedIndividual(
											IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
									OWLClass cls = dft
											.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
									OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
									AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
									mng.applyChange(addAxiom1);
									try {
										mng.saveOntology(ont);
									} catch (OWLOntologyStorageException e) {
										System.out.println(e.getMessage());
									}

									// STORE TRIPLE PATTERN
									ctriples.add(tp);
									if (ctriplesn.containsKey(tp.getSubject())) {
										if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {

											ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
										} else {
											Set<Node> content = new HashSet<Node>();
											content.add(tp.getObject());
											ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
										}
									} else {
										Set<Node> content = new HashSet<Node>();
										content.add(tp.getObject());
										Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
										map.put(tp.getPredicate(), content);
										ctriplesn.put(tp.getSubject(), map);
									}

									// ADD TRIPLE PATTERN
									OWLNamedIndividual ni = null;
									ni = dft.getOWLNamedIndividual(
											IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
									OWLNamedIndividual ni2 = null;
									ni2 = dft.getOWLNamedIndividual(
											IRI.create(tp.getObject().getNameSpace() + tp.getObject().getLocalName()));
									OWLObjectProperty o = dft.getOWLObjectProperty(IRI.create(
											tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
									OWLAxiom axiom = dft.getOWLObjectPropertyAssertionAxiom(o, ni, ni2);
									AddAxiom addAxiom = new AddAxiom(ont, axiom);
									mng.applyChange(addAxiom);
									try {
										mng.saveOntology(ont);
									} catch (OWLOntologyStorageException e) {
										System.out.println(e.getMessage());
									}

								} else {
									if (!wrong_analysis) {
										System.out.println("<p style=\"color:green\">"
												+ "Class or Individual used as data property:" + "</p>");
										System.out.println("<p> Triple: " + print(tp) + "</p>");
										wrong_analysis = true;
									}
								}
							} else { /* second V should be an object property */
								if (tp.getSubject().isVariable()) /* VVU */ {

									// ADD TYPE
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
										System.out.println(e.getMessage());
									}
								} else if (tp.getSubject().isURI()) /* UVU */ {
									/* V should be an object property */

									// ADD TYPE
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
										System.out.println(e.getMessage());
									}
								} else /* LVU */ {
									System.out.println("<p style=\"color:green\">"
											+ "Literal cannot be used as subject:" + "</p>");
									System.out.println("<p> Triple: " + print(tp) + "</p>");
									wrong_analysis = true;
								}
							}
						} else {
							if (tp.getPredicate().isLiteral()) /* ULU */
							{
								System.out.println(
										"<p style=\"color:green\">" + "Literal cannot be a property:" + "</p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
								wrong_analysis = true;
							} else if (tp.getPredicate().isURI()) /* UUU */ {

								// STORE TRIPLE PATTERN
								ctriples.add(tp);
								if (ctriplesn.containsKey(tp.getSubject())) {
									if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {
										ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
									} else {
										Set<Node> content = new HashSet<Node>();
										content.add(tp.getObject());
										ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
									}
								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
									map.put(tp.getPredicate(), content);
									ctriplesn.put(tp.getSubject(), map);
								}

								// ADD TRIPLE PATTERN
								OWLNamedIndividual ni3 = null;
								ni3 = dft.getOWLNamedIndividual(
										IRI.create(tp.getSubject().getNameSpace() + tp.getSubject().getLocalName()));
								OWLNamedIndividual ni4 = null;
								ni4 = dft.getOWLNamedIndividual(
										IRI.create(tp.getObject().getNameSpace() + tp.getObject().getLocalName()));
								if (isObjectPropertyAll(tp.getPredicate().getNameSpace(),
										tp.getPredicate().getLocalName())) {
									OWLObjectProperty o = dft.getOWLObjectProperty(IRI.create(
											tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
									OWLAxiom axiom = dft.getOWLObjectPropertyAssertionAxiom(o, ni3, ni4);
									AddAxiom addAxiom = new AddAxiom(ont, axiom);
									mng.applyChange(addAxiom);
									try {
										mng.saveOntology(ont);
									} catch (OWLOntologyStorageException e) {
										System.out.println(e.getMessage());
									}
								} else {
									System.out.println("<p style=\"color:green\">"
											+ "Individual used with a data property:" + "</p>");
									System.out.println("<p> Triple: " + print(tp) + "</p>");
									wrong_analysis = true;
								}
							}
						}
					}
				}

				else if (tp.getSubject().isLiteral()) /* L-V */ {
					System.out.println("<p style=\"color:green\">" + "Literal cannot be used as subject:" + "</p>");
					System.out.println("<p> Triple: " + print(tp) + "</p>");
					wrong_analysis = true;
				} else if (tp.getSubject().isVariable()) {
					if (tp.getPredicate().isLiteral()) /* VLV */
					{
						System.out.println("<p style=\"color:green\">" + "Literal cannot be a predicate:" + "</p>");
						System.out.println("<p> Triple: " + print(tp) + "</p>");
						wrong_analysis = true;
					} else if (tp.getPredicate().isURI()) /* VUV */
					{

						if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
								&& !isObjectPropertyAll(tp.getPredicate().getNameSpace(),
										tp.getPredicate().getLocalName())) {

							// STORE TRIPLE PATTERN
							ctriples.add(tp);
							if (ctriplesn.containsKey(tp.getSubject())) {
								if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {

									ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
								}
							} else {
								Set<Node> content = new HashSet<Node>();
								content.add(tp.getObject());
								Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
								map.put(tp.getPredicate(), content);
								ctriplesn.put(tp.getSubject(), map);
							}

							// ADD TYPE
							OWLNamedIndividual ni1 = null;
							ni1 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

							OWLClass cls1 = dft
									.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls1, ni1);
							AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
							mng.applyChange(addAxiom1);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							OWLClass cls2 = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
							OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls2, ni2);
							AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);
							mng.applyChange(addAxiom2);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}

							// ADD TYPE
							OWLNamedIndividual ni3 = null;
							ni3 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							for (String t : RangesDataPropertyAll(
									IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()))) {
								OWLClass cls3 = dft.getOWLClass(
										IRI.create("http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1)));
								OWLAxiom axiom3 = dft.getOWLClassAssertionAxiom(cls3, ni3);
								AddAxiom addAxiom3 = new AddAxiom(ont, axiom3);
								mng.applyChange(addAxiom3);
								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									System.out.println(e.getMessage());
								}
								addTypeVariable(tp.getObject().getName().substring(0).toUpperCase(),
										"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
								types_literals.put(tp.getObject().getName(),
										"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
							}
						} else if (isObjectPropertyAll(tp.getPredicate().getNameSpace(),
								tp.getPredicate().getLocalName())
								&& !isDataPropertyAll(tp.getPredicate().getNameSpace(),
										tp.getPredicate().getLocalName())) {

							// ADD TYPE
							OWLNamedIndividual ni1 = null;
							ni1 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

							OWLClass cls1 = dft
									.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls1, ni1);
							AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
							mng.applyChange(addAxiom1);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							OWLClass cls2 = dft
									.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom2 = dft.getOWLClassAssertionAxiom(cls2, ni2);
							AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);
							mng.applyChange(addAxiom2);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}

							// STORE TRIPLE PATTERN

							ctriples.add(tp);
							if (ctriplesn.containsKey(tp.getSubject())) {
								if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {
									ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
								}
							} else {
								Set<Node> content = new HashSet<Node>();
								content.add(tp.getObject());
								Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
								map.put(tp.getPredicate(), content);
								ctriplesn.put(tp.getSubject(), map);
							}

							// ADD TRIPLE PATTERN
							OWLNamedIndividual ni3 = null;
							ni3 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

							OWLNamedIndividual ni4 = null;
							ni4 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							OWLObjectProperty o = dft.getOWLObjectProperty(
									IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
							OWLAxiom axiom3 = dft.getOWLObjectPropertyAssertionAxiom(o, ni3, ni4);
							AddAxiom addAxiom3 = new AddAxiom(ont, axiom3);
							mng.applyChange(addAxiom3);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {

								System.out.println(e.getMessage());
							}
						} else {
							if (!wrong_analysis) {
								wrong_analysis = true;
								System.out.println(
										"<p style=\"color:green\">" + "Class or Individual used as property:" + "</p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
							}
						}

					} else /* VVV */
					{

						// ADD TYPE
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
							System.out.println(e.getMessage());
						}
					}
				} else {
					if (tp.getPredicate().isLiteral()) /* ULV */ {
						System.out.println("<p style=\"color:green\">" + "Literal cannot be a predicate:" + "</p>");
						System.out.println("<p> Triple: " + print(tp) + "</p>");
						wrong_analysis = true;
					} else if (tp.getPredicate().isURI()) /* UUV */
					{
						if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
								&& !isObjectPropertyAll(tp.getPredicate().getNameSpace(),
										tp.getPredicate().getLocalName())) {

							// STORE TRIPLE PATTERN
							ctriples.add(tp);
							if (ctriplesn.containsKey(tp.getSubject())) {
								if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {
									ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
								}
							} else {
								Set<Node> content = new HashSet<Node>();
								content.add(tp.getObject());
								Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
								map.put(tp.getPredicate(), content);
								ctriplesn.put(tp.getSubject(), map);
							}

							// ADD TYPE
							OWLNamedIndividual ni1 = null;
							ni1 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
							OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
							AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
							mng.applyChange(addAxiom1);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}

							// ADD TYPE
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
									System.out.println(e.getMessage());
								}
								addTypeVariable(tp.getObject().getName().substring(0).toUpperCase(),
										"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
								types_literals.put(tp.getObject().getName(),
										"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
							}
						} else if (isObjectPropertyAll(tp.getPredicate().getNameSpace(),
								tp.getPredicate().getLocalName())
								&& !isDataPropertyAll(tp.getPredicate().getNameSpace(),
										tp.getPredicate().getLocalName())) {

							// ADD TYPE
							OWLNamedIndividual ni1 = null;
							ni1 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
							OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
							AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
							mng.applyChange(addAxiom1);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}

							// STORE TRIPLE PATTERN
							ctriples.add(tp);
							if (ctriplesn.containsKey(tp.getSubject())) {
								if (ctriplesn.get(tp.getSubject()).containsKey(tp.getPredicate())) {
									ctriplesn.get(tp.getSubject()).get(tp.getPredicate()).add(tp.getObject());
								} else {
									Set<Node> content = new HashSet<Node>();
									content.add(tp.getObject());
									ctriplesn.get(tp.getSubject()).put(tp.getPredicate(), content);
								}
							} else {
								Set<Node> content = new HashSet<Node>();
								content.add(tp.getObject());
								Map<Node, Set<Node>> map = new HashMap<Node, Set<Node>>();
								map.put(tp.getPredicate(), content);
								ctriplesn.put(tp.getSubject(), map);
							}

							// ADD TRIPLE PATTERN
							OWLNamedIndividual ni2 = null;
							ni2 = dft.getOWLNamedIndividual(
									IRI.create(tp.getSubject().getNameSpace() + tp.getSubject().getLocalName()));
							OWLNamedIndividual ni3 = null;
							ni3 = dft.getOWLNamedIndividual(
									IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
							OWLObjectProperty o = dft.getOWLObjectProperty(
									IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
							OWLAxiom axiom2 = dft.getOWLObjectPropertyAssertionAxiom(o, ni2, ni3);
							AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);
							mng.applyChange(addAxiom2);
							try {
								mng.saveOntology(ont);
							} catch (OWLOntologyStorageException e) {
								System.out.println(e.getMessage());
							}
						} else {
							if (!wrong_analysis) {
								wrong_analysis = true;
								System.out.println(
										"<p style=\"color:green\">" + "Class or Individual used as property:" + "</p>");
								System.out.println("<p> Triple: " + print(tp) + "</p>");
							}
						}
					} else /* UVV */
					{
						// ADD TYPE
						OWLNamedIndividual ni = null;
						ni = dft.getOWLNamedIndividual(
								IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
						OWLAxiom axiom = dft.getOWLClassAssertionAxiom(cls, ni);
						AddAxiom addAxiom2 = new AddAxiom(ont, axiom);
						mng.applyChange(addAxiom2);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							System.out.println(e.getMessage());
						}
					}
				}
			} else {
			}
		} // NON LINEAR
		else {

			if (!wrong_analysis) {
				wrong_analysis = true;
				System.out
						.println("<p style=\"color:green\">" + "Query is not linear. Found same property in:" + "</p>");
				System.out.println("<p>" + tp.getSubject() + "</p>");
			}

		}

	};

	public List<List<String>> SPARQL_ANALYSIS(String file, String queryString, Integer step) {

		Set<OWLAxiom> axs = ontology.getABoxAxioms(true);
		for (OWLAxiom ax : axs) {

			manager.removeAxiom(ontology, ax);

		}
		try {
			manager.saveOntology(ontology);
		} catch (OWLOntologyStorageException e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
		}

		OWLClass lit = dataFactory.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
		OWLClass res = dataFactory.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
		OWLClass dt = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:dateTime"));
		OWLClass st = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:string"));
		OWLClass intt = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:integer"));
		OWLClass pintt = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:positiveInteger"));
		OWLClass nintt = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:negativeInteger"));
		OWLClass npintt = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:nonPositiveInteger"));
		OWLClass nnintt = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:nonNegativeInteger"));
		OWLClass dou = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:double"));
		OWLClass flo = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:float"));
		OWLClass dec = dataFactory.getOWLClass(IRI.create("http://www.types.org#xsd:decimal"));

		OWLDisjointClassesAxiom ax0 = dataFactory.getOWLDisjointClassesAxiom(lit, res);
		OWLDisjointClassesAxiom ax1 = dataFactory.getOWLDisjointClassesAxiom(dt, st);
		OWLDisjointClassesAxiom ax2 = dataFactory.getOWLDisjointClassesAxiom(dt, intt);
		OWLDisjointClassesAxiom ax3 = dataFactory.getOWLDisjointClassesAxiom(dt, pintt);
		OWLDisjointClassesAxiom ax4 = dataFactory.getOWLDisjointClassesAxiom(dt, nintt);
		OWLDisjointClassesAxiom ax5 = dataFactory.getOWLDisjointClassesAxiom(dt, npintt);
		OWLDisjointClassesAxiom ax6 = dataFactory.getOWLDisjointClassesAxiom(dt, nnintt);
		OWLDisjointClassesAxiom ax7 = dataFactory.getOWLDisjointClassesAxiom(dt, dou);
		OWLDisjointClassesAxiom ax8 = dataFactory.getOWLDisjointClassesAxiom(dt, flo);
		OWLDisjointClassesAxiom ax9 = dataFactory.getOWLDisjointClassesAxiom(dt, dec);

		OWLDisjointClassesAxiom ax10 = dataFactory.getOWLDisjointClassesAxiom(st, intt);
		OWLDisjointClassesAxiom ax11 = dataFactory.getOWLDisjointClassesAxiom(st, pintt);
		OWLDisjointClassesAxiom ax12 = dataFactory.getOWLDisjointClassesAxiom(st, nintt);
		OWLDisjointClassesAxiom ax13 = dataFactory.getOWLDisjointClassesAxiom(st, npintt);
		OWLDisjointClassesAxiom ax14 = dataFactory.getOWLDisjointClassesAxiom(st, nnintt);
		OWLDisjointClassesAxiom ax15 = dataFactory.getOWLDisjointClassesAxiom(st, dou);
		OWLDisjointClassesAxiom ax16 = dataFactory.getOWLDisjointClassesAxiom(st, flo);
		OWLDisjointClassesAxiom ax17 = dataFactory.getOWLDisjointClassesAxiom(st, dec);
		OWLDisjointClassesAxiom ax18 = dataFactory.getOWLDisjointClassesAxiom(nintt, pintt);

		OWLDisjointClassesAxiom ax19 = dataFactory.getOWLDisjointClassesAxiom(dou, intt);
		OWLDisjointClassesAxiom ax20 = dataFactory.getOWLDisjointClassesAxiom(dou, pintt);
		OWLDisjointClassesAxiom ax21 = dataFactory.getOWLDisjointClassesAxiom(dou, nintt);
		OWLDisjointClassesAxiom ax22 = dataFactory.getOWLDisjointClassesAxiom(dou, npintt);
		OWLDisjointClassesAxiom ax23 = dataFactory.getOWLDisjointClassesAxiom(dou, nnintt);

		OWLDisjointClassesAxiom ax24 = dataFactory.getOWLDisjointClassesAxiom(flo, intt);
		OWLDisjointClassesAxiom ax25 = dataFactory.getOWLDisjointClassesAxiom(flo, pintt);
		OWLDisjointClassesAxiom ax26 = dataFactory.getOWLDisjointClassesAxiom(flo, nintt);
		OWLDisjointClassesAxiom ax27 = dataFactory.getOWLDisjointClassesAxiom(flo, npintt);
		OWLDisjointClassesAxiom ax28 = dataFactory.getOWLDisjointClassesAxiom(flo, nnintt);

		OWLDisjointClassesAxiom ax29 = dataFactory.getOWLDisjointClassesAxiom(dec, intt);
		OWLDisjointClassesAxiom ax30 = dataFactory.getOWLDisjointClassesAxiom(dec, pintt);
		OWLDisjointClassesAxiom ax31 = dataFactory.getOWLDisjointClassesAxiom(dec, nintt);
		OWLDisjointClassesAxiom ax32 = dataFactory.getOWLDisjointClassesAxiom(dec, npintt);
		OWLDisjointClassesAxiom ax33 = dataFactory.getOWLDisjointClassesAxiom(dec, nnintt);

		AddAxiom addAxiom0 = new AddAxiom(ontology, ax0);
		manager.applyChange(addAxiom0);
		AddAxiom addAxiom1 = new AddAxiom(ontology, ax1);
		manager.applyChange(addAxiom1);
		AddAxiom addAxiom2 = new AddAxiom(ontology, ax2);
		manager.applyChange(addAxiom2);
		AddAxiom addAxiom3 = new AddAxiom(ontology, ax3);
		manager.applyChange(addAxiom3);
		AddAxiom addAxiom4 = new AddAxiom(ontology, ax4);
		manager.applyChange(addAxiom4);
		AddAxiom addAxiom5 = new AddAxiom(ontology, ax5);
		manager.applyChange(addAxiom5);
		AddAxiom addAxiom6 = new AddAxiom(ontology, ax6);
		manager.applyChange(addAxiom6);
		AddAxiom addAxiom7 = new AddAxiom(ontology, ax7);
		manager.applyChange(addAxiom7);
		AddAxiom addAxiom8 = new AddAxiom(ontology, ax8);
		manager.applyChange(addAxiom8);
		AddAxiom addAxiom9 = new AddAxiom(ontology, ax9);
		manager.applyChange(addAxiom9);
		AddAxiom addAxiom10 = new AddAxiom(ontology, ax10);
		manager.applyChange(addAxiom10);
		AddAxiom addAxiom11 = new AddAxiom(ontology, ax11);
		manager.applyChange(addAxiom11);
		AddAxiom addAxiom12 = new AddAxiom(ontology, ax12);
		manager.applyChange(addAxiom12);
		AddAxiom addAxiom13 = new AddAxiom(ontology, ax13);
		manager.applyChange(addAxiom13);
		AddAxiom addAxiom14 = new AddAxiom(ontology, ax14);
		manager.applyChange(addAxiom14);
		AddAxiom addAxiom15 = new AddAxiom(ontology, ax15);
		manager.applyChange(addAxiom15);
		AddAxiom addAxiom16 = new AddAxiom(ontology, ax16);
		manager.applyChange(addAxiom16);
		AddAxiom addAxiom17 = new AddAxiom(ontology, ax17);
		manager.applyChange(addAxiom17);
		AddAxiom addAxiom18 = new AddAxiom(ontology, ax18);
		manager.applyChange(addAxiom18);
		/*
		 * AddAxiom addAxiom19 = new AddAxiom(ontology, ax19);
		 * manager.applyChange(addAxiom19); AddAxiom addAxiom20 = new AddAxiom(ontology,
		 * ax20); manager.applyChange(addAxiom20); AddAxiom addAxiom21 = new
		 * AddAxiom(ontology, ax21); manager.applyChange(addAxiom21); AddAxiom
		 * addAxiom22 = new AddAxiom(ontology, ax22); manager.applyChange(addAxiom22);
		 * AddAxiom addAxiom23 = new AddAxiom(ontology, ax23);
		 * manager.applyChange(addAxiom23); AddAxiom addAxiom24 = new AddAxiom(ontology,
		 * ax24); manager.applyChange(addAxiom24); AddAxiom addAxiom25 = new
		 * AddAxiom(ontology, ax25); manager.applyChange(addAxiom25); AddAxiom
		 * addAxiom26 = new AddAxiom(ontology, ax26); manager.applyChange(addAxiom26);
		 * AddAxiom addAxiom27 = new AddAxiom(ontology, ax27);
		 * manager.applyChange(addAxiom27); AddAxiom addAxiom28 = new AddAxiom(ontology,
		 * ax28); manager.applyChange(addAxiom28); AddAxiom addAxiom29 = new
		 * AddAxiom(ontology, ax29); manager.applyChange(addAxiom29); AddAxiom
		 * addAxiom30 = new AddAxiom(ontology, ax30); manager.applyChange(addAxiom30);
		 * AddAxiom addAxiom31 = new AddAxiom(ontology, ax31);
		 * manager.applyChange(addAxiom31); AddAxiom addAxiom32 = new AddAxiom(ontology,
		 * ax32); manager.applyChange(addAxiom32); AddAxiom addAxiom33 = new
		 * AddAxiom(ontology, ax33); manager.applyChange(addAxiom33);
		 */

		try {
			manager.saveOntology(ontology);
		} catch (OWLOntologyStorageException e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
		}

		final Query query = QueryFactory.create(queryString);
		if (query.isConstructType() || query.isAskType() || query.isDescribeType() || query.isDistinct()
				|| query.hasAggregators() || query.hasOrderBy() || query.hasGroupBy() || query.hasHaving()
				|| query.hasOffset() || !query.getGraphURIs().isEmpty() || !query.getNamedGraphURIs().isEmpty()
				|| query.hasLimit()) {
			System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
			System.out.println("<p>" + query + "</p>");
			wrong_analysis = true;
			rules.clear();
		} else {
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
			String urio = ontology.getOntologyID().getOntologyIRI().toString();
			for (TriplePath tp : ctriples) {
				datatriples.add(tp);
				if (tp.getSubject().isVariable()) {

					datatriples.add(tp);
					Set<OWLClassExpression> typ = ClassOfVariable(
							IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));

					if (!(typ == null)) {
						for (OWLClassExpression c : typ) {
							OWLRestriction(c.asOWLClass(), tp.getSubject());
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

			System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
			System.out.println("<p>" + el + "</p>");
			wrong_analysis = true;
			rules.clear();

		} else if (el.getExpr().getFunction().getFunctionName(null) == "notexists") {
			System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
			System.out.println("<p>" + el + "</p>");
			wrong_analysis = true;
			rules.clear();

		} else if (el.getExpr().getFunction().getFunctionName(null) == "and") {

			for (int i = 1; i <= el.getExpr().getFunction().numArgs(); i++) {
				ElementFilter e = new ElementFilter(el.getExpr().getFunction().getArg(i));
				elementFilter(e, step, fileo);
			}

		}

		else if ((el.getExpr().getFunction().getOpName().toString() == "<")
				|| (el.getExpr().getFunction().getOpName().toString() == "<=")
				|| (el.getExpr().getFunction().getOpName().toString() == "=")
				|| (el.getExpr().getFunction().getOpName().toString() == ">")
				|| (el.getExpr().getFunction().getOpName().toString() == ">=")
				|| (el.getExpr().getFunction().getOpName().toString() == "!=")) {
			nvar++;
			constraints_elements.add(
					"( " + el.getExpr().getFunction().getArgs().get(0) + " " + el.getExpr().getFunction().getOpName()
							+ " " + el.getExpr().getFunction().getArgs().get(1) + " )");

			List<String> ss = new ArrayList<>(SExprtoPTerm(el.getExpr(), null));
			for (int i = 0; i < ss.size(); i++) {
				rules.get(current).add(ss.get(i));
			}
		} else {
			wrong_analysis = true;
			System.out.println("<p style=\"color:green\">" + "Expression "
					+ el.getExpr().getFunction().getFunctionName(null) + " not allowed in FILTER expression." + "</p>");

		}
	}

	public void elementBind(ElementBind el, Integer step, String fileo) {

		nvar++;
		List<String> ss = new ArrayList<>(SExprtoPTerm(el.getExpr(), el.getVar().asNode()));
		for (int i = 0; i < ss.size(); i++) {
			rules.get(current).add(ss.get(i));
		}
		constraints_elements.add(el.getExpr().toString() + " = " + el.getVar().asNode().toString());
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
		}
	};

	public void elementUnion(ElementUnion el, Integer step, String fileo) {

		System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
		System.out.println("<p>" + el + "</p>");
		wrong_analysis = true;
		rules.clear();
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
				System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
				System.out.println("<p>" + e + "</p>");
				wrong_analysis = true;
				rules.clear();
			}
		}
	}

	public void elementMinus(ElementMinus el, Integer step, String fileo) {
		System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
		System.out.println("<p>" + el + "</p>");
		wrong_analysis = true;
		rules.clear();
	}

	public void elementOptional(ElementOptional el, Integer step, String fileo) {
		System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
		System.out.println("<p>" + el + "</p>");
		wrong_analysis = true;
		rules.clear();
	};

	public void elementSubQuery(ElementSubQuery el, Integer step, String fileo) {

		Element e = el.getQuery().getQueryPattern();

		Query query = el.getQuery();

		if (query.isConstructType() || query.isAskType() || query.isDescribeType() || query.isDistinct()
				|| query.hasAggregators() || query.hasOrderBy() || query.hasGroupBy() || query.hasHaving()
				|| query.hasOffset() || !query.getGraphURIs().isEmpty() || !query.getNamedGraphURIs().isEmpty()
				|| query.hasLimit()) {
			System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
			System.out.println("<p>" + query + "</p>");
			wrong_analysis = true;
			rules.clear();
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
			System.out.println("<p style=\"color:green\">" + "SPARQL expression not supported:" + "</p>");
			System.out.println("<p>" + e + "</p>");
			wrong_analysis = true;
			rules.clear();
		}
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		for (TriplePath tp : ctriples) {

			datatriples.add(tp);
			Set<OWLClassExpression> typ = ClassOfVariable(
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
			if (!(typ == null)) {
				for (OWLClassExpression c : typ) {
					OWLRestriction(c.asOWLClass(), tp.getSubject());
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

	public void OWLRestriction(OWLClass ce, Node var_name) {

		OWLClassExpressionVisitor cv = new OWLClassExpressionVisitor() {

			@Override
			public void visit(OWLClass arg0) {

				Set<OWLClassExpression> ec = arg0.getEquivalentClasses(ontology);
				for (OWLClassExpression e : ec) {
					e.accept(this);
				}
				Set<OWLClassExpression> sc = arg0.getSuperClasses(ontology);
				for (OWLClassExpression e : sc) {
					e.accept(this);
				}
			}

			@Override
			public void visit(OWLObjectIntersectionOf arg0) {
				Set<OWLClassExpression> ec = arg0.getOperands();
				for (OWLClassExpression e : ec) {
					e.accept(this);
				}
			}

			@Override
			public void visit(OWLObjectUnionOf arg0) {

				show = false;
				Boolean one = false;
				Set<OWLClassExpression> ec = arg0.getOperands();

				for (OWLClassExpression e : ec) {
					if (!one) {
						e.accept(this);
					}
					one = !wrong_analysis;
				}
				show = true;

			}

			@Override
			public void visit(OWLObjectComplementOf arg0) {

				negation = true;
				show = false;
				OWLClassExpression neg = arg0.getOperand();
				neg.accept(this);
				show = true;
				negation = false;
				wrong_analysis = !wrong_analysis;

			}

			@Override
			public void visit(OWLObjectSomeValuesFrom arg0) {
				if (ctriplesn.containsKey(var_name)) {
					OWLObjectSomeValuesFrom someValuesFrom = (OWLObjectSomeValuesFrom) arg0;
					OWLClassExpression filler = someValuesFrom.getFiller();
					for (OWLObjectProperty dp : someValuesFrom.getObjectPropertiesInSignature()) {
						Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {
							Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
							Boolean one = false;
							for (Node var : vars_) {
								if (!one) {
									OWLRestriction(filler.asOWLClass(), var);
								}
								one = !wrong_analysis;
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLObjectAllValuesFrom arg0) {
				if (ctriplesn.containsKey(var_name)) {
					OWLObjectAllValuesFrom allValuesFrom = (OWLObjectAllValuesFrom) arg0;
					OWLClassExpression filler = allValuesFrom.getFiller();
					for (OWLObjectProperty dp : allValuesFrom.getObjectPropertiesInSignature()) {
						Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {
							Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
							for (Node var : vars_) {
								OWLRestriction(filler.asOWLClass(), var);
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLObjectHasValue arg0) {
				if (ctriplesn.containsKey(var_name)) {
					OWLObjectHasValue hasValue = (OWLObjectHasValue) arg0;
					OWLObjectProperty dp = hasValue.getProperty().asOWLObjectProperty();
					OWLIndividual ind = hasValue.getValue();

					Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
					if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {
						Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
						Boolean one = false;
						for (Node var : vars_) {
							if (!one) {
								if (var.equals(NodeFactory.createURI(ind.toString()))) {
									one = true;
								}
							}
						}
						wrong_analysis = !one;

					}
				}

			}

			@Override
			public void visit(OWLObjectMinCardinality arg0) {
			}

			@Override
			public void visit(OWLObjectExactCardinality arg0) {
			}

			@Override
			public void visit(OWLObjectMaxCardinality arg0) {
			}

			@Override
			public void visit(OWLObjectHasSelf arg0) {
			}

			@Override
			public void visit(OWLObjectOneOf arg0) {
			}

			@Override
			public void visit(OWLDataAllValuesFrom arg0) {

				if (negation) {
					if (!wrong_analysis && show) {
						wrong_analysis = true;
						System.out.println(
								"<p style=\"color:magenta\">" + "Negated OWL Restriction not allowed:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
					}
				} else {
					if (ctriplesn.containsKey(var_name)) {
						OWLDataAllValuesFrom allValuesFrom = (OWLDataAllValuesFrom) arg0;
						OWLDataRange filler = allValuesFrom.getFiller();
						for (OWLDataProperty dp : allValuesFrom.getDataPropertiesInSignature()) {
							Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
							if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {
								Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
								String cons = "";

								if (filler instanceof OWLDatatypeRestriction) {
									OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;

									for (Node var : vars_) {

										if (r.getDatatype().isInteger()) {
											for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
												if (fr.getFacet().toString() == "maxExclusive") {
													if (var.isVariable()) {
														cons = cons + var.toString().substring(1).toUpperCase() + "#<"
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + var.getLiteralValue().toString() + "#<"
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													}

												} else if (fr.getFacet().toString() == "maxInclusive") {
													if (var.isVariable()) {
														cons = cons + var.toString().substring(1).toUpperCase() + "#=<"
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " <= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + var.getLiteralValue().toString() + "#=<"
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " <= " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minExclusive") {
													if (var.isVariable()) {
														cons = cons + var.toString().substring(1).toUpperCase() + "#>"
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + var.getLiteralValue().toString() + "#>"
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minInclusive") {
													if (var.isVariable()) {
														cons = cons + var.toString().substring(1).toUpperCase() + "#>="
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + var.getLiteralValue().toString() + "#>="
																+ fr.getFacetValue().getLiteral() + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													}
												}
											}
										} else if (r.getDatatype().isFloat() || r.getDatatype().isDouble()) {
											for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
												if (fr.getFacet().toString() == "maxExclusive") {

													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ "<" + fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + "<"
																+ fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "maxInclusive") {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ "=<" + fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " <= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + "=<"
																+ fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("(" + var.getLiteralValue().toString()
																+ " <= " + fr.getFacetValue().getLiteral() + ")");
													}
												} else if (fr.getFacet().toString() == "minExclusive") {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ ">" + fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + ">"
																+ fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minInclusive") {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ ">=" + fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + ">="
																+ fr.getFacetValue().getLiteral() + "}" + ",";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													}
												}
											}
										} else {
											if (!wrong_analysis && show) {
												wrong_analysis = true;
												System.out.println("<p style=\"color:magenta\">"
														+ "OWL Restriction not allowed:" + "</p>");
												ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
												System.out.println("<p>" + rendering.render(arg0) + "</p>");
											}
										}
									}
									if (!cons.isEmpty()) {
										cons = cons.substring(0, cons.length() - 1);
									}

									rules.get(current).add(cons);

								} else {
									// NON OWL DATATYPE RESTRICTION

								}
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLDataSomeValuesFrom arg0) {
				if (!wrong_analysis && show) {
					wrong_analysis = true;
					System.out.println("<p style=\"color:magenta\">" + "OWL Restriction not allowed:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
				}
			}

			@Override
			public void visit(OWLDataHasValue arg0) {
				if (negation) {
					if (!wrong_analysis && show) {
						wrong_analysis = true;
						System.out.println(
								"<p style=\"color:magenta\">" + "Negated OWL Restriction not allowed:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
					}
				} else {
					if (ctriplesn.containsKey(var_name)) {
						OWLDataHasValue HasValue = (OWLDataHasValue) arg0;
						OWLLiteral value = HasValue.getValue();
						for (OWLDataProperty dp : HasValue.getDataPropertiesInSignature()) {
							Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
							if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {
								Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
								String cons = "";
								for (Node var : vars_) {
									if (value.isInteger()) {
										if (var.isVariable()) {
											cons = cons + var.toString().substring(1).toUpperCase() + "#="
													+ value.getLiteral();
											constraints_elements.add("( " + var.toString().toUpperCase() + " = "
													+ value.getLiteral() + " )");
										} else {
											cons = cons + var.getLiteralValue().toString() + "#=" + value.getLiteral();
											constraints_elements.add("( " + var.getLiteralValue().toString() + " = "
													+ value.getLiteral() + " )");
										}
									} else if (value.isFloat() || value.isDouble()) {
										if (var.isVariable()) {
											cons = cons + "{" + var.toString().substring(1).toUpperCase() + "=:="
													+ value.getLiteral() + "}";
											constraints_elements.add("( " + var.toString().toUpperCase() + " = "
													+ value.getLiteral() + " )");
										} else {
											cons = cons + "{" + var.getLiteralValue().toString() + "=:="
													+ value.getLiteral() + "}";
											constraints_elements.add("( " + var.getLiteralValue().toString() + " = "
													+ value.getLiteral() + " )");
										}
									} else {
										if (!wrong_analysis && show) {
											wrong_analysis = true;
											System.out.println("<p style=\"color:magenta\">"
													+ "OWL Restriction not allowed:" + "</p>");
											ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
											System.out.println("<p>" + rendering.render(arg0) + "</p>");
										}
									}
								}
								if (!cons.isEmpty()) {
									cons = cons.substring(0, cons.length() - 1);
								}

								rules.get(current).add(cons);
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLDataMinCardinality arg0) {
				if (!wrong_analysis && show) {
					wrong_analysis = true;
					System.out.println("<p style=\"color:magenta\">" + "OWL Restriction not allowed:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
				}
			}

			@Override
			public void visit(OWLDataExactCardinality arg0) {
				if (!wrong_analysis && show) {
					wrong_analysis = true;
					System.out.println("<p style=\"color:magenta\">" + "OWL Restriction not allowed:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
				}
			}

			@Override
			public void visit(OWLDataMaxCardinality arg0) {
				if (!wrong_analysis && show) {
					wrong_analysis = true;
					System.out.println("<p style=\"color:magenta\">" + "OWL Restriction not allowed:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
				}
			}
		};
		ce.accept(cv);
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
		} else if (st.isLiteral()) {
			if (st.getLiteralDatatypeURI() == null) {
				if (st.toString().startsWith("\"#")) {
					pt = st.toString().replaceAll("\"", "");
				} else {
					pt = st.toString() + "^^" + "'http://www.w3.org/2001/XMLSchema#string'";
				}
			} else {
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
			} else if (st.isFunction()) {
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
						types_literals.put("B" + act, types_literals.get("A" + act));
						addTypeVariable("B" + act, types_literals.get("A" + act));
					} else if (types_literals.containsKey("B" + act)) {
						types_literals.put("A" + act, types_literals.get("B" + act));
						addTypeVariable("A" + act, types_literals.get("B" + act));
					} else {
					}
					if (types_literals.containsKey("B" + act)) {
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
						} else if (types_literals.get("B" + act)
								.equals("http://www.types.org#xsd:nonNegativeInteger")) {
							String Op = "";
							if (st.getFunction().getOpName().equals("!=")) {
								Op = "#\\=";
							} else if (st.getFunction().getOpName().equals("<=")) {
								Op = "#=<";
							} else {
								Op = "#" + st.getFunction().getOpName();
							}
							pt.add("A" + act + Op + "B" + act);
							pt.add("B" + act + "#>=0");
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
							pt.add("B" + act + "#>0");
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
							pt.add("B" + act + "#<0");
						} else if (types_literals.get("B" + act)
								.equals("http://www.types.org#xsd:nonPositiveInteger")) {
							String Op = "";
							if (st.getFunction().getOpName().equals("!=")) {
								Op = "#\\=";
							} else if (st.getFunction().getOpName().equals("<=")) {
								Op = "#=<";
							} else {
								Op = "#" + st.getFunction().getOpName();
							}
							pt.add("A" + act + Op + "B" + act);
							pt.add("B" + act + "#=<0");
						} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:double")
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
						} else {
						}
					} else {
					}
					nvar++;
				} else {
				}
			}
		} else if (st.isVariable()) {
			String v = var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase();
			String sv = st.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase();
			if (types_literals.containsKey(sv)) {
				types_literals.put(v, types_literals.get(sv));
				addTypeVariable(v, types_literals.get(sv));
				if (types_literals.containsKey(v)) {
					if (types_literals.get(v).equals("http://www.types.org#xsd:integer")
							|| types_literals.get(v).equals("http://www.types.org#xsd:string")
							|| types_literals.get(v).equals("http://www.types.org#xsd:dateTime")) {
						pt.add(sv + "#=" + v);
					} else if (types_literals.get(v).equals("http://www.types.org#xsd:positiveInteger")) {
						pt.add(sv + "#=" + v);
						pt.add("0#<" + v);
					} else if (types_literals.get(v).equals("http://www.types.org#xsd:negativeInteger")) {
						pt.add(sv + "#=" + sv);
						pt.add("0#>" + v);
					} else if (types_literals.get(v).equals("http://www.types.org#xsd:nonNegativeInteger")) {
						pt.add(sv + "#=" + v);
						pt.add("0#=<" + v);
					} else if (types_literals.get(v).equals("http://www.types.org#xsd:nonPositivoInteger")) {
						pt.add(sv + "#=" + v);
						pt.add("0#>=" + v);
					} else if (types_literals.get(v).equals("http://www.types.org#xsd:float")
							|| types_literals.get(v).equals("http://www.types.org#xsd:double")
							|| types_literals.get(v).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + sv + "=:=" + v + " }");
					} else {
						if (!wrong_analysis) {
							System.out.print(
									"<p style=\"color:green\">" + "The following variable is not typed: " + "</p>");
							System.out.println("<p>" + v + "</p>");
							wrong_analysis = true;
						}
					}
				} else {
					if (!wrong_analysis) {
						System.out
								.print("<p style=\"color:green\">" + "The following variable is not typed: " + "</p>");
						System.out.println("<p>" + v + "</p>");
						wrong_analysis = true;
					}
				}
			} else {
				if (!wrong_analysis) {
					System.out.print("<p style=\"color:green\">" + "The following variable is not typed: " + "</p>");
					System.out.println("<p>" + sv + "</p>");
					wrong_analysis = true;
				}
			}

		} else if (st.isConstant()) {

			if (st.toString().endsWith("^^<http://www.w3.org/2001/XMLSchema#dateTime>")) {
				String date = st.toString().split("\"")[1];
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:dateTime");
				DateTimeFormatter fomatter = DateTimeFormatter.ofPattern("yyyy-MM-dd'T'HH:mm:ss'Z'", Locale.ENGLISH);
				LocalDateTime ldt = LocalDateTime.parse(date, fomatter);
				Integer result = ldt.hashCode();
				pt.add(result + "#=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if (isInteger(st.toString())) {
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:integer");
				pt.add(st.toString() + "#=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if ((isReal(st.toString()))) {
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:float");
				pt.add(st.toString() + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			}

			else {
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:string");
				int MAX_LENGTH = 13;
				long result = 0;
				for (int i = 0; i < st.toString().length(); i++)
					result += pow(27, MAX_LENGTH - i - 1) * (1 + st.toString().charAt(i));
				pt.add(result + "#=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			}
		} else if (st.isFunction()) {
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
				if (types_literals.containsKey("A" + act)) {
					if (types_literals.get("A" + act).equals("http://www.types.org#xsd:integer")
							|| types_literals.get("A" + act).equals("http://www.types.org#xsd:string")
							|| types_literals.get("A" + act).equals("http://www.types.org#xsd:dateTime")) {
						pt.add("A" + act + "#=" + "U" + act);
					} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:positiveInteger")) {
						pt.add("A" + act + "#=" + "U" + act);
						pt.add("A" + act + "#>0");
					} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:negativeInteger")) {
						pt.add("A" + act + "#=" + "U" + act);
						pt.add("A" + act + "#<0");
					} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
						pt.add("A" + act + "#=" + "U" + act);
						pt.add("A" + act + "#>=0");
					} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
						pt.add("A" + act + "#=" + "U" + act);
						pt.add("A" + act + "#=<0");
					} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:float")
							|| types_literals.get("A" + act).equals("http://www.types.org#xsd:double")
							|| types_literals.get("A" + act).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + "A" + act + "=:=" + "U" + act + " }");
					} else {
					}
				} else {
				}

				if (types_literals.containsKey("B" + act)) {
					if (types_literals.get("B" + act).equals("http://www.types.org#xsd:integer")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:string")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:dateTime")) {
						pt.add("B" + act + "#=" + "V" + act);
					} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:positiveInteger")) {
						pt.add("B" + act + "#=" + "V" + act);
						pt.add("B" + act + "#>0");
					} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:negativeInteger")) {
						pt.add("B" + act + "#=" + "V" + act);
						pt.add("B" + act + "#<0");
					} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
						pt.add("B" + act + "#=" + "V" + act);
						pt.add("B" + act + "#>=0");
					} else if (types_literals.get("A" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
						pt.add("B" + act + "#=" + "V" + act);
						pt.add("B" + act + "#=<0");
					} else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:double")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:float")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + "B" + act + " =:= " + "V" + act + " }");
					} else {
					}
				} else {
				}
				types_literals.put("W" + act, types_literals.get("U" + act));
				if (types_literals.containsKey("W" + act)) {
					if (types_literals.get("W" + act).equals("http://www.types.org#xsd:integer")
							|| types_literals.get("W" + act).equals("http://www.types.org#xsd:string")
							|| types_literals.get("W" + act).equals("http://www.types.org#xsd:dateTime")) {
						pt.add("W" + act + "#=" + "U" + act + st.getFunction().getOpName() + "V" + act);
					} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:positiveInteger")) {
						pt.add("W" + act + "#=" + "U" + act + st.getFunction().getOpName() + "V" + act);
						pt.add("W" + act + "#>0");
					} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:negativeInteger")) {
						pt.add("W" + act + "#=" + "U" + act + st.getFunction().getOpName() + "V" + act);
						pt.add("W" + act + "#<0");
					} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:nonNegativeInteger")) {
						pt.add("W" + act + "#=" + "U" + act + st.getFunction().getOpName() + "V" + act);
						pt.add("W" + act + "#>=0");
					} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:nonPositiveInteger")) {
						pt.add("W" + act + "#=" + "U" + act + st.getFunction().getOpName() + "V" + act);
						pt.add("W" + act + "#=<0");
					} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:float")
							|| types_literals.get("W" + act).equals("http://www.types.org#xsd:double")
							|| types_literals.get("W" + act).equals("http://www.types.org#xsd:decimal"))

					{
						pt.add("{" + "W" + act + "=:=" + "U" + act + st.getFunction().getOpName() + "V" + act + "}");
					} else {
					}
				} else {
				}
				String res = var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase();
				types_literals.put(res, types_literals.get("W" + act));
				if (types_literals.containsKey(res)) {
					if (types_literals.get(res).equals("http://www.types.org#xsd:integer")
							|| types_literals.get(res).equals("http://www.types.org#xsd:string")
							|| types_literals.get(res).equals("http://www.types.org#xsd:dateTime")) {
						pt.add(res + "#=" + "W" + act);
					} else if (types_literals.get(res).equals("http://www.types.org#xsd:positiveInteger")) {
						pt.add(res + "#=" + "W" + act);
						pt.add(res + "#>0");
					} else if (types_literals.get(res).equals("http://www.types.org#xsd:negativeInteger")) {
						pt.add(res + "#=" + "W" + act);
						pt.add(res + "#<0");
					} else if (types_literals.get(res).equals("http://www.types.org#xsd:nonNegativeInteger")) {
						pt.add(res + "#=" + "W" + act);
						pt.add(res + "#>=0");
					} else if (types_literals.get(res).equals("http://www.types.org#xsd:nonPositiveInteger")) {
						pt.add(res + "#=" + "W" + act);
						pt.add(res + "#=<0");
					} else if (types_literals.get(res).equals("http://www.types.org#xsd:float")
							|| types_literals.get(res).equals("http://www.types.org#xsd:double")
							|| types_literals.get(res).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + res + "=:=" + "W" + act + " }");
					} else {
						if (!wrong_analysis) {
							System.out.print(
									"<p style=\"color:green\">" + "The following variable is not typed: " + "</p>");
							System.out.println("<p>" + res + "</p>");
							wrong_analysis = true;
						}
					}
				} else {
					if (!wrong_analysis) {
						System.out
								.print("<p style=\"color:green\">" + "The following variable is not typed: " + "</p>");
						System.out.println("<p>" + res + "</p>");
						wrong_analysis = true;
					}
				}
				nvar++;
			} else {
			}
		}
		return pt;
	}

	public void addTypeVariable(String variable, String type) {
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		OWLNamedIndividual ni = dataFactory.getOWLNamedIndividual(IRI.create(urio + '#' + variable));
		if (type == null) {
			wrong_analysis = true;
			System.out.print("<p style=\"color:green\">" + "The following variable is not typed: " + "</p>");
			System.out.println("<p>" + variable + "</p>");
		} else {
			OWLClass cls = dataFactory.getOWLClass(IRI.create(type));
			OWLClass cls2 = dataFactory.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
			OWLAxiom axiom1 = dataFactory.getOWLClassAssertionAxiom(cls, ni);
			OWLAxiom axiom2 = dataFactory.getOWLClassAssertionAxiom(cls2, ni);
			AddAxiom addAxiom1 = new AddAxiom(ontology, axiom1);
			AddAxiom addAxiom2 = new AddAxiom(ontology, axiom2);
			manager.applyChange(addAxiom1);
			manager.applyChange(addAxiom2);
			try {
				manager.saveOntology(ontology);
			} catch (OWLOntologyStorageException e) {
				// TODO Auto-generated catch block
				System.out.println(e.getMessage());
			}
		}
	}

	public void addTypeAssertion(OWLClassExpression cls, OWLNamedIndividual ni) {
		OWLAxiom axiom1 = dataFactory.getOWLClassAssertionAxiom(cls, ni);
		AddAxiom addAxiom1 = new AddAxiom(ontology, axiom1);
		manager.applyChange(addAxiom1);
		try {
			manager.saveOntology(ontology);
		} catch (OWLOntologyStorageException e) {
			System.out.println(e.getMessage());
		}

	}

	public void removeTypeAssertion(OWLClassExpression cls, OWLNamedIndividual ni) {
		OWLAxiom axiom1 = dataFactory.getOWLClassAssertionAxiom(cls, ni);
		RemoveAxiom addAxiom1 = new RemoveAxiom(ontology, axiom1);
		manager.applyChange(addAxiom1);
		try {
			manager.saveOntology(ontology);
		} catch (OWLOntologyStorageException e) {
			System.out.println(e.getMessage());
		}

	}

	public long pow(long a, int b) {
		if (b == 0)
			return 1;
		if (b == 1)
			return a;
		if (b % 2 == 0)
			return pow(a * a, b / 2);
		else
			return a * pow(a * a, b / 2);
	}

	public void SPARQL_CORRECTNESS(String query) throws Exception {

		Set<OWLAxiom> axioms = ontology.getTBoxAxioms(true);
		Boolean warning1 = false;
		Boolean warning2 = false;

		for (OWLAxiom ax : axioms) {
			if (ax.isOfType(AxiomType.FUNCTIONAL_DATA_PROPERTY) && !warning1) {
				warning1 = true;
				System.out.println(
						"<p style=\"color:grey;\">Warning: The ontology contains a functional data property assertion.</p>");
			}
			if (ax.isOfType(AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION) & !warning2) {
				warning2 = true;
				System.out.println(
						"<p style=\"color:grey;\">Warning: The ontology contains a negative data property assertion.</p>");
			}
		}

		copy(file);
		next = 1;
		current = 0;
		nvar = 0;
		vars.clear();
		rules.clear();
		SPARQL_ANALYSIS(file, query, 0);

		String r = "";
		if (!wrong_analysis) {
			r = sparql_consistency();
			if (r == "true") {
				r = sparql_constraint_checking();
				if (r == "true") {
					System.out.println("<p style=\"color:DodgerBlue;\">Successful correctness checking</p>");
				} else {
					System.out.println("<p style=\"color:Tomato;\">Unsuccessful correctness checking due to:</p>");
					System.out.print("<p>" + r + "</p>");
				}
			} else {
				System.out.println("<p style=\"color:Tomato;\">Unsuccessful correctness checking due to:</p>");
				System.out.print("<p>" + r + "</p>");
				for (List<String> rule : rules) {
					for (int i = 1; i < rule.size(); i++) {
						System.out.println("<p>" + rule.get(i).replace("#", "") + "</p>");
					}
				}
			}
		} else {
		}
		restore(file);
	};

	public void SPARQL_TYPE_VALIDITY(String query, String var_name, String type_name) throws Exception {
		copy(file);
		next = 1;
		current = 0;
		nvar = 0;
		vars.clear();
		rules.clear();
		SPARQL_ANALYSIS(file, query, 0);
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		OWLClass ce = dataFactory.getOWLClass(IRI.create(type_name));
		OWLNamedIndividual in = dataFactory.getOWLNamedIndividual(IRI.create(urio + '#' + var_name));
		owl_type_validity(ce, in, NodeFactory.createVariable(var_name));
		if (!error && !wrong_analysis) {
			System.out.println("<p style=\"color:DodgerBlue;\">"
					+ "Successful type validity checking. The property has been proved.</p>");
		}
		restore(file);
	};

	public void owl_type_validity(OWLClass ce, OWLNamedIndividual in, Node var_name) {
		OWLClassExpressionVisitor cv = new OWLClassExpressionVisitor() {
			@Override
			public void visit(OWLClass arg0) {
				OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
				String entailment = entailment(axiom);
				if (entailment == "true") {
				} else {

					Set<OWLClassExpression> ec0 = arg0.getEquivalentClasses(ontology);

					for (OWLClassExpression e : ec0) {

						if (!error) {

							e.accept(this);
						}
					}
					 
					if (error) {}
					else if (!ec0.isEmpty()) {}
					else {
						addTypeAssertion(arg0, in);
						OWLClass res = dataFactory
								.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
						addTypeAssertion(res, in);
						String consistency = consistency();
						
						if (consistency == "true") {

							Set<OWLClassExpression> ec1 = arg0.getSuperClasses(ontology);
							for (OWLClassExpression e : ec1) {
								if (!error) {
									e.accept(this);
								}
							}
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}

						}
						removeTypeAssertion(arg0, in);
					}
					}
				
			}

			@Override
			public void visit(OWLObjectIntersectionOf arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					Set<OWLClassExpression> ec = arg0.getOperands();

					for (OWLClassExpression e : ec) {
						if (!error) {

							e.accept(this);
						}
					}
				}

			}

			@Override
			public void visit(OWLObjectUnionOf arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					show = false;
					Boolean one = false;
					Set<OWLClassExpression> ec = arg0.getOperands();
					for (OWLClassExpression e : ec) {
						if (!one) {
							e.accept(this);
							one = !error;
						}
					}
					show = true;
					if (!one) {
						System.out.println("<p style=\"color:red\">"
								+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
								+ "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						printClass(rendering.render(arg0), rendering.render(in));
					}
				}
			}

			@Override
			public void visit(OWLObjectComplementOf arg0) {

				negation = true;
				show = false;
				OWLClassExpression neg = arg0.getOperand();
				neg.accept(this);
				show = true;
				negation = false;
				error = !error;
				if (!error && show) {
					System.out.println("<p style=\"color:red\">"
							+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
							+ "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					printClass(rendering.render(arg0), rendering.render(in));
				}
			}

			@Override
			public void visit(OWLObjectSomeValuesFrom arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					if (ctriplesn.containsKey(var_name)) {
						OWLObjectSomeValuesFrom someValuesFrom = (OWLObjectSomeValuesFrom) arg0;
						OWLClassExpression filler = someValuesFrom.getFiller();
						Boolean prop = false;

						for (OWLObjectProperty dp : someValuesFrom.getObjectPropertiesInSignature()) {
							Map<Node, Set<Node>> uses = ctriplesn.get(var_name);

							if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {

								Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
								Boolean one = false;
								for (Node var : vars_) {
									String urio = ontology.getOntologyID().getOntologyIRI().toString();
									OWLNamedIndividual in = dataFactory.getOWLNamedIndividual(
											IRI.create(urio + '#' + var.toString().substring(1)));
									if (!one) {
										owl_type_validity(filler.asOWLClass(), in, var);
									}
									if (!error) {
										one = true;
									}
								}
							} else {
								prop = true;
							}
						}
						if (prop) {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}
						}

					} else {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					}

					addTypeAssertion(arg0, in);
					String consistency = consistency();
					if (consistency == "true") {

						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}

					} else {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
									+ "</p>");
							System.out.print(explanations());
						}
					}
					removeTypeAssertion(arg0, in);
				}
			}

			@Override
			public void visit(OWLObjectAllValuesFrom arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					if (ctriplesn.containsKey(var_name)) {
						OWLObjectAllValuesFrom allValuesFrom = (OWLObjectAllValuesFrom) arg0;
						OWLClassExpression filler = allValuesFrom.getFiller();
						Boolean prop = false;
						for (OWLObjectProperty dp : allValuesFrom.getObjectPropertiesInSignature()) {
							Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
							if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {
								Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
								for (Node var : vars_) {
									String urio = ontology.getOntologyID().getOntologyIRI().toString();
									OWLNamedIndividual in = dataFactory.getOWLNamedIndividual(
											IRI.create(urio + '#' + var.toString().substring(1)));
									owl_type_validity(filler.asOWLClass(), in, var);
								}
							} else {
								prop = true;
							}
						}
						if (prop) {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}
						}

					} else {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					}

					addTypeAssertion(arg0, in);
					String consistency = consistency();
					if (consistency == "true") {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
									+ "</p>");
							System.out.print(explanations());
						}
					}
					removeTypeAssertion(arg0, in);
				}
			}

			@Override
			public void visit(OWLObjectHasValue arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {

						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {

							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectMinCardinality arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {

							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectExactCardinality arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {

							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectMaxCardinality arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {

							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectHasSelf arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {

							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectOneOf arg0) {
				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						if (!error && show) {
							error = true;
							System.out.println("<p style=\"color:red\">"
									+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
									+ "</p>");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {

							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}

						} else {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
										+ "</p>");
								System.out.print(explanations());
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLDataAllValuesFrom arg0) {

				if (!error && show) {
					System.out.println("<p style=\"color:magenta\">"
							+ "This type cannot be proved by type validity analysis:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
					error = true;
				}

			}

			@Override
			public void visit(OWLDataSomeValuesFrom arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					if (arg0.isObjectRestriction()) {
						OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
						String entailment = entailment(axiom);
						if (entailment == "false") {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}
						} else {
							addTypeAssertion(arg0, in);
							String consistency = consistency();
							if (consistency == "true") {

								if (!error && show) {
									error = true;
									System.out.println("<p style=\"color:red\">"
											+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
											+ "</p>");
									ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
									printClass(rendering.render(arg0), rendering.render(in));
								}

							} else {
								if (!error && show) {
									error = true;
									System.out.println("<p style=\"color:red\">"
											+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
											+ "</p>");
									System.out.print(explanations());
								}

							}
							removeTypeAssertion(arg0, in);
						}
					} else { // arg0.isDataRestriction()

						if (ctriplesn.containsKey(var_name)) {

							String t1n = "use_module(library('clpfd'))";
							org.jpl7.Query q1n = new org.jpl7.Query(t1n);
							System.out.print((q1n.hasSolution() ? "" : ""));
							String t2n = "use_module(library('clpr'))";
							org.jpl7.Query q2n = new org.jpl7.Query(t2n);
							System.out.print((q2n.hasSolution() ? "" : ""));
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
								String drn = rule.get(0);
								org.jpl7.Query drqn = new org.jpl7.Query("retractall(" + drn + ")");
								System.out.print((drqn.hasSolution() ? "" : ""));
								String aprulen = "asserta((" + c + "))";
								org.jpl7.Query q4n = new org.jpl7.Query(aprulen);
								System.out.print((q4n.hasSolution() ? "" : ""));
							}
							OWLDataSomeValuesFrom someValuesFrom = (OWLDataSomeValuesFrom) arg0;
							OWLDataRange filler = someValuesFrom.getFiller();

							for (OWLDataProperty dp : someValuesFrom.getDataPropertiesInSignature()) {
								Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
								if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString())))

								{

									Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));

									if (filler instanceof OWLDatatypeRestriction) {

										OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;

										String domain = "";

										for (Node v : vars_) {
											if (v.isVariable()) {
												if (types_literals
														.containsKey(v.toString().substring(1).toUpperCase())) {
													if (types_literals.get(v.toString().substring(1).toUpperCase())
															.equals("http://www.types.org#xsd:integer")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:string")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:dateTime")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:positiveInteger")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:negativeInteger")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:nonPositiveInteger")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:nonNegativeInteger")) {
														Integer act = nvar;
														nvar++;
														domain = domain + "fd_dom("
																+ v.toString().substring(1).toUpperCase() + ",R" + act
																+ ")" + ",";
														rename.put("R" + act, v.toString().substring(1).toUpperCase());

													} else {
														if (types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:float")
																|| types_literals
																		.get(v.toString().substring(1).toUpperCase())
																		.equals("http://www.types.org#xsd:double")
																|| types_literals
																		.get(v.toString().substring(1).toUpperCase())
																		.equals("http://www.types.org#xsd:decimal")) {
															Integer act = nvar;
															nvar++;
															domain = domain + "(sup("
																	+ v.toString().substring(1).toUpperCase() + ",S),"
																	+ "inf(" + v.toString().substring(1).toUpperCase()
																	+ ",I)->R" + act + "=..['..',I,S];" + "(sup("
																	+ v.toString().substring(1).toUpperCase() + ",S)->R"
																	+ act + "=..['..',inf,S];" + "inf("
																	+ v.toString().substring(1).toUpperCase() + ",I)->R"
																	+ act + "=..['..',I,sup];" + "R" + act
																	+ "=..['..',inf,sup]))" + ",";
															rename.put("R" + act,
																	v.toString().substring(1).toUpperCase());
														}
													}
												}
											}
										}

										if (!domain.isEmpty()) {
											domain = domain.substring(0, domain.length() - 1);
										}

										String poshead = "";
										for (int i = 1; i < rules.get(0).size(); i++) {
											poshead = poshead + rules.get(0).get(i) + ',';
										}

										String cons = "";
										for (Node var : vars_) {

											if (r.getDatatype().isInteger()) {
												for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
													if (fr.getFacet().toString() == "maxExclusive") {

														if (var.isVariable()) {
															cons = cons + var.toString().substring(1).toUpperCase()
																	+ "#<" + fr.getFacetValue().getLiteral() + ",";
														} else {
															cons = cons + var.getLiteralValue().toString() + "#<"
																	+ fr.getFacetValue().getLiteral() + ",";
														}

													} else if (fr.getFacet().toString() == "maxInclusive") {
														if (var.isVariable()) {
															cons = cons + var.toString().substring(1).toUpperCase()
																	+ "#=<" + fr.getFacetValue().getLiteral() + ",";
														} else {
															cons = cons + var.getLiteralValue().toString() + "#=<"
																	+ fr.getFacetValue().getLiteral() + ",";
														}

													} else if (fr.getFacet().toString() == "minExclusive") {
														if (var.isVariable()) {
															cons = cons + var.toString().substring(1).toUpperCase()
																	+ "#>" + fr.getFacetValue().getLiteral() + ",";
														} else {
															cons = cons + var.getLiteralValue().toString() + "#>"
																	+ fr.getFacetValue().getLiteral() + ",";
														}

													} else if (fr.getFacet().toString() == "minInclusive") {
														if (var.isVariable()) {
															cons = cons + var.toString().substring(1).toUpperCase()
																	+ "#>=" + fr.getFacetValue().getLiteral() + ",";
														} else {
															cons = cons + var.getLiteralValue().toString() + "#>="
																	+ fr.getFacetValue().getLiteral() + ",";
														}
													}
												}
											} else if (r.getDatatype().isFloat() || r.getDatatype().isDouble()) {
												for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
													if (fr.getFacet().toString() == "maxExclusive") {
														if (var.isVariable()) {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + "<"
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														} else {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + "<"
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														}
													} else if (fr.getFacet().toString() == "maxInclusive") {
														if (var.isVariable()) {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + "=<"
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														} else {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + "=<"
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														}
													} else if (fr.getFacet().toString() == "minExclusive") {
														if (var.isVariable()) {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + ">"
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														} else {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + ">"
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														}
													} else if (fr.getFacet().toString() == "minInclusive") {
														if (var.isVariable()) {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + ">="
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														} else {
															cons = cons + "{"
																	+ var.toString().substring(1).toUpperCase() + ">="
																	+ fr.getFacetValue().getLiteral() + "}" + ",";
														}
													}
												}
											} else {
												if (!error && show) {
													error = true;
													System.out.println("<p style=\"color:magenta\">"
															+ "OWL Restriction not allowed:" + "</p>");
													ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
													System.out.println("<p>" + rendering.render(arg0) + "</p>");
												}
											}
										}
										if (!cons.isEmpty()) {
											cons = cons.substring(0, cons.length() - 1);
										}
										String phead;

										if (!poshead.isEmpty()) {
											poshead = poshead.substring(0, poshead.length() - 1);
											if (!domain.isEmpty()) {
												phead = poshead + "," + cons + "," + domain;
											} else {
												phead = poshead + "," + cons;
											}
										} else {
											if (!domain.isEmpty()) {
												phead = cons + "," + domain;
											} else {
												phead = cons;
											}
										}

										org.jpl7.Query qcons = new org.jpl7.Query(phead);

										if (!qcons.hasSolution()) {
											// INCONSISTENCY
											if (!error && show) {
												error = true;
												System.out.println("<p style=\"color:red\">"
														+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
														+ "</p>");
												if (!poshead.isEmpty()) {
													System.out.println("<p>" + poshead.replace("#", "") + ","
															+ cons.replace("#", "") + "</p>");
												} else {
													System.out.println("<p>" + cons.replace("#", "") + "</p>");
												}

											}
										} else {

											String negcons = "";
											for (Node var : vars_) {

												if (r.getDatatype().isInteger()) {
													for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
														if (fr.getFacet().toString() == "maxExclusive") {
															if (var.isVariable()) {
																negcons = negcons
																		+ var.toString().substring(1).toUpperCase()
																		+ "#>=" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " >= "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + var.getLiteralValue().toString()
																		+ "#>=" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " >= "
																		+ fr.getFacetValue().getLiteral() + " )");
															}
														} else if (fr.getFacet().toString() == "maxInclusive") {
															if (var.isVariable()) {
																negcons = negcons
																		+ var.toString().substring(1).toUpperCase()
																		+ "#>" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " > "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + var.getLiteralValue().toString()
																		+ "#>" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " > "
																		+ fr.getFacetValue().getLiteral() + " )");
															}
														} else if (fr.getFacet().toString() == "minExclusive") {
															if (var.isVariable()) {
																negcons = negcons
																		+ var.toString().substring(1).toUpperCase()
																		+ "#=<" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " =< "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + var.getLiteralValue().toString()
																		+ "#=<" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " =< "
																		+ fr.getFacetValue().getLiteral() + " )");
															}
														} else if (fr.getFacet().toString() == "minInclusive") {
															if (var.isVariable()) {
																negcons = negcons
																		+ var.toString().substring(1).toUpperCase()
																		+ "#<" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " < "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + var.getLiteralValue().toString()
																		+ "#<" + fr.getFacetValue().getLiteral() + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " < "
																		+ fr.getFacetValue().getLiteral() + ")");
															}
														}
													}
												} else if (r.getDatatype().isDouble() || r.getDatatype().isFloat()) {
													for (OWLFacetRestriction fr : r.getFacetRestrictions()) {

														if (fr.getFacet().toString() == "maxExclusive") {

															if (var.isVariable()) {
																negcons = negcons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ ">=" + fr.getFacetValue().getLiteral() + "}"
																		+ ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " >= "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + "{"
																		+ var.getLiteralValue().toString() + ">="
																		+ fr.getFacetValue().getLiteral() + "}" + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " >= "
																		+ fr.getFacetValue().getLiteral() + " )");
															}

														} else if (fr.getFacet().toString() == "maxInclusive") {
															if (var.isVariable()) {
																negcons = negcons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ ">" + fr.getFacetValue().getLiteral() + "}"
																		+ ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " > "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + "{"
																		+ var.getLiteralValue().toString() + ">"
																		+ fr.getFacetValue().getLiteral() + "}" + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " > "
																		+ fr.getFacetValue().getLiteral() + " )");
															}
														} else if (fr.getFacet().toString() == "minExclusive") {
															if (var.isVariable()) {
																negcons = negcons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ "=<" + fr.getFacetValue().getLiteral() + "}"
																		+ ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " =< "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + "{"
																		+ var.getLiteralValue().toString() + "=<"
																		+ fr.getFacetValue().getLiteral() + "}" + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " =< "
																		+ fr.getFacetValue().getLiteral() + " )");
															}
														} else if (fr.getFacet().toString() == "minInclusive") {
															if (var.isVariable()) {
																negcons = negcons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ "<" + fr.getFacetValue().getLiteral() + "}"
																		+ ";";
																constraints_elements.add("( "
																		+ var.toString().toUpperCase() + " < "
																		+ fr.getFacetValue().getLiteral() + " )");
															} else {
																negcons = negcons + "{"
																		+ var.getLiteralValue().toString() + "<"
																		+ fr.getFacetValue().getLiteral() + "}" + ";";
																constraints_elements.add("( "
																		+ var.getLiteralValue().toString() + " < "
																		+ fr.getFacetValue().getLiteral() + " )");
															}
														}
													}
												} else {
													if (!error && show) {
														error = true;
														System.out.println("<p style=\"color:green\">"
																+ "OWL Restriction not allowed:" + "</p>");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														System.out.println("<p>" + rendering.render(arg0) + "</p>");
													}
												}
											}

											if (!negcons.isEmpty()) {
												negcons = negcons.substring(0, negcons.length() - 1);
											}

											String neghead = "";
											for (int i = 1; i < rules.get(0).size(); i++) {
												neghead = neghead + rules.get(0).get(i) + ',';
											}

											String nhead;

											if (!neghead.isEmpty()) {
												neghead = neghead.substring(0, neghead.length() - 1);
												if (!domain.isEmpty()) {
													nhead = neghead + "," + negcons + "," + domain;
												} else {
													nhead = neghead + "," + negcons;
												}
											} else {
												if (!domain.isEmpty()) {
													nhead = negcons + "," + domain;
												} else {
													nhead = negcons;
												}
											}

											org.jpl7.Query qimpl = new org.jpl7.Query(nhead);

											if (qimpl.hasSolution())
											// COUNTEREXAMPLE
											{
												if (neghead.isEmpty()) {
													if (!error && show) {
														error = true;
														System.out.print("<p style=\"color:red\">"
																+ "Unsuccessful type validity checking. The property cannot be proved. "
																+ "Not enough information for: " + "</p>");
														System.out.println(
																"<p>" + dp.getIRI().toString().split("#")[1] + "</p>");
													}
												} else {
													if (!error && show) {
														error = true;
														System.out.println("<p style=\"color:red\">"
																+ "Unsuccessful type validity checking. Counterexample:"
																+ "</p>");
														Map<String, Term>[] sols = qimpl.allSolutions();
														for (Map<String, Term> s : sols) {
															for (String key : s.keySet())
																if (s.get(key).isCompound()) {
																	System.out.println("<p>" + rename.get(key) + "="
																			+ s.get(key) + "</p>");
																}
														}
													}
												}
											}

											else {
												// ENTAILMENT
												String ihead;
												ihead = phead + "->" + cons;
												qcons = new org.jpl7.Query(ihead);
												if (qcons.hasSolution()) {
												} else {
													if (!error && show) {
														error = true;
														System.out.println("<p style=\"color:red\">"
																+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
																+ "</p>");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														printClass(rendering.render(arg0), rendering.render(in));
													}
												}

											}
										}

									} else {
										// NON OWL DATATYPE RESTRICTION
									}
								} else {
									// INCOMPLETENESS
									if (!error && show) {
										error = true;
										System.out.print("<p style=\"color:red\">"
												+ "Unsuccessful type validity checking. The property cannot be proved. "
												+ "Not enough information for: " + "</p>");
										System.out.println("<p>" + dp.getIRI().toString().split("#")[1] + "</p>");
									}
								}
							}
						} else {
							// INCOMPLETENESS
							if (!error && show) {
								error = true;
								System.out.print("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The property cannot be proved. "
										+ "Not enough information for: " + "</p>");
								System.out.println("<p>" + var_name + "</p>");
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLDataHasValue arg0) {

				if (negation) {
					if (!error && show) {
						System.out.println("<p style=\"color:magenta\">"
								+ "This type cannot be proved by type validity analysis:" + "</p>");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						System.out.println("<p>" + rendering.render(arg0) + "</p>");
						error = true;
					}
				} else {
					if (arg0.isObjectRestriction()) {
						OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
						String entailment = entailment(axiom);
						if (entailment == "false") {
							if (!error && show) {
								error = true;
								System.out.println("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
										+ "</p>");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							}
						} else {
							addTypeAssertion(arg0, in);
							String consistency = consistency();

							if (consistency == "true") {

								if (!error && show) {
									error = true;
									System.out.println("<p style=\"color:red\">"
											+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
											+ "</p>");
									ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
									printClass(rendering.render(arg0), rendering.render(in));
								}

							} else {
								if (!error && show) {
									error = true;
									System.out.println("<p style=\"color:red\">"
											+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
											+ "</p>");
									System.out.print(explanations());
								}
							}
							removeTypeAssertion(arg0, in);
						}
					} else { // arg0.isDataRestriction()
						if (ctriplesn.containsKey(var_name)) {
							String t1n = "use_module(library('clpfd'))";
							org.jpl7.Query q1n = new org.jpl7.Query(t1n);
							System.out.print((q1n.hasSolution() ? "" : ""));
							String t2n = "use_module(library('clpr'))";
							org.jpl7.Query q2n = new org.jpl7.Query(t2n);
							System.out.print((q2n.hasSolution() ? "" : ""));
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
								String drn = rule.get(0);
								org.jpl7.Query drqn = new org.jpl7.Query("retractall(" + drn + ")");
								System.out.print((drqn.hasSolution() ? "" : ""));
								String aprulen = "asserta((" + c + "))";
								org.jpl7.Query q4n = new org.jpl7.Query(aprulen);
								System.out.print((q4n.hasSolution() ? "" : ""));
							}
							OWLDataHasValue hasValue = (OWLDataHasValue) arg0;
							OWLLiteral val = hasValue.getValue();
							for (OWLDataProperty dp : hasValue.getDataPropertiesInSignature()) {
								Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
								if (uses.containsKey(NodeFactory.createURI(dp.getIRI().toString()))) {

									Set<Node> vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));

									String domain = "";
									for (Node v : vars_) {
										if (v.isVariable()) {
											if (types_literals.containsKey(v.toString().substring(1).toUpperCase())) {
												if (types_literals.get(v.toString().substring(1).toUpperCase())
														.equals("http://www.types.org#xsd:integer")
														|| types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:string")
														|| types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:dateTime")
														|| types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:positiveInteger")
														|| types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:negativeInteger")
														|| types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:nonPositiveInteger")
														|| types_literals.get(v.toString().substring(1).toUpperCase())
																.equals("http://www.types.org#xsd:nonNegativeInteger")) {
													Integer act = nvar;
													nvar++;
													domain = domain + "fd_dom("
															+ v.toString().substring(1).toUpperCase() + ",R" + act + ")"
															+ ",";
													rename.put("R" + act, v.toString().substring(1).toUpperCase());
												} else {
													if (types_literals.get(v.toString().substring(1).toUpperCase())
															.equals("http://www.types.org#xsd:float")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:double")
															|| types_literals
																	.get(v.toString().substring(1).toUpperCase())
																	.equals("http://www.types.org#xsd:decimal")) {
														Integer act = nvar;
														nvar++;
														domain = domain + "(sup("
																+ v.toString().substring(1).toUpperCase() + ",S),"
																+ "inf(" + v.toString().substring(1).toUpperCase()
																+ ",I)->R" + act + "=..['..',I,S];" + "(sup("
																+ v.toString().substring(1).toUpperCase() + ",S)->R"
																+ act + "=..['..',inf,S];" + "inf("
																+ v.toString().substring(1).toUpperCase() + ",I)->R"
																+ act + "=..['..',I,sup];" + "R" + act
																+ "=..['..',inf,sup]))" + ",";
														rename.put("R" + act, v.toString().substring(1).toUpperCase());
													}
												}
											}
										}
									}
									if (!domain.isEmpty()) {
										domain = domain.substring(0, domain.length() - 1);
									}

									{

										vars_ = uses.get(NodeFactory.createURI(dp.getIRI().toString()));
										String poscons = "";
										for (Node var : vars_) {

											if (val.isInteger()) {
												if (var.isVariable()) {
													poscons = poscons + var.toString().substring(1).toUpperCase() + "#="
															+ val.getLiteral();
												} else {
													poscons = poscons + var.getLiteral() + "#=" + val.getLiteral();
												}
											} else if (val.isFloat() || val.isDouble()) {
												if (var.isVariable()) {
													poscons = poscons + "{" + var.toString().substring(1).toUpperCase()
															+ "=:=" + val.getLiteral() + "}";
												} else {
													poscons = poscons + "{" + var.getLiteral() + "=:="
															+ val.getLiteral() + "}";
												}
											} else {
												if (!error && show) {
													error = true;
													System.out.println("<p style=\"color:magenta\">"
															+ "OWL Restriction not allowed:" + "</p>");
													ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
													System.out.println("<p>" + rendering.render(arg0) + "</p>");
												}
											}
										}
										String poshead = "";
										for (int i = 1; i < rules.get(0).size(); i++) {
											poshead = poshead + rules.get(0).get(i) + ',';
										}
										String phead;
										 
										
										if (!poshead.isEmpty()) {
											poshead = poshead.substring(0, poshead.length() - 1);
											if (!domain.isEmpty()) {
												phead = poshead + "," + poscons + "," + domain;
											} else {
												phead = poshead + "," + poscons;
											}
										} else {
											if (!domain.isEmpty()) {
												phead = poscons + "," + domain;
											} else {
												phead = poscons;
											}
										}

										org.jpl7.Query qcons = new org.jpl7.Query(phead);
										if (!qcons.hasSolution()) {
											// INCONSISTENCY
											if (!error && show) {
												error = true;
												System.out.println("<p style=\"color:red\">"
														+ "Unsuccessful type validity checking. Caused by the following inconsistency:"
														+ "</p>");
												System.out.println("<p>" + phead.replace("#", "") + "</p>");
											}
										} else {

											String neghead = "";
											for (int i = 1; i < rules.get(0).size(); i++) {
												neghead = neghead + rules.get(0).get(i) + ',';
											}

											String negcons = "";
											for (Node var : vars_) {
												if (val.isInteger()) {
													if (var.isVariable()) {
														negcons = negcons + "#\\"
																+ var.toString().substring(1).toUpperCase() + "#="
																+ val.getLiteral();
														constraints_elements.add("(" + var.toString().toUpperCase()
																+ "=" + val.getLiteral() + ")");
													} else {
														negcons = negcons + "#\\" + var.getLiteralValue().toString()
																+ "#=" + val.getLiteral();
														constraints_elements.add("(" + var.getLiteralValue().toString()
																+ "=" + val.getLiteral() + ")");
													}
												} else if (val.isFloat() || val.isDouble()) {
													if (var.isVariable()) {
														negcons = negcons + "#\\"
																+ var.toString().substring(1).toUpperCase() + "=:="
																+ val.getLiteral();
														constraints_elements.add("(" + var.toString().toUpperCase()
																+ "=" + val.getLiteral() + ")");
													} else {
														negcons = negcons + "#\\" + var.getLiteralValue().toString()
																+ "=:=" + val.getLiteral();
														constraints_elements.add("(" + var.getLiteralValue().toString()
																+ "=" + val.getLiteral() + ")");
													}
												}
											}

											 

											String nhead;
											if (!neghead.isEmpty()) {
												neghead = neghead.substring(0, neghead.length() - 1);
												if (!domain.isEmpty()) {
													nhead = neghead + "," + negcons + "," + domain;
												} else {
													nhead = neghead + "," + negcons;
												}
											} else {
												if (!domain.isEmpty()) {
													nhead = negcons + "," + domain;
												} else {
													nhead = negcons;
												}
											}


											org.jpl7.Query qimpl = new org.jpl7.Query(nhead);
											if (qimpl.hasSolution()) {
												// COUNTEREXAMPLE

												if (neghead.isEmpty()) {
													if (!error && show) {
														error = true;
														System.out.print("<p style=\"color:red\">"
																+ "Unsuccessful type validity checking. The property cannot be proved. "
																+ "Not enough information for: " + "</p>");
														System.out.println(
																"<p>" + dp.getIRI().toString().split("#")[1] + "</p>");
													}
												} else {
													if (!error && show) {
														error = true;
														System.out.println("<p style=\"color:red\">"
																+ "Unsuccessful type validity checking. Counterexample:"
																+ "</p>");
														Map<String, Term>[] sols = qimpl.allSolutions();
														for (Map<String, Term> s : sols) {
															for (String key : s.keySet())
																if (s.get(key).isCompound()) {
																	System.out.println("<p>" + rename.get(key) + "="
																			+ s.get(key) + "</p>");
																}
														}
													}
												}
											} else

											{
												// ENTAILMENT
												phead = poshead + "->" + poscons;
												qcons = new org.jpl7.Query(phead);
												if (qcons.hasSolution()) {
												} else {
													if (!error && show) {
														error = true;
														System.out.println("<p style=\"color:red\">"
																+ "Unsuccessful type validity checking. The following class membership cannot be proved:"
																+ "</p>");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														printClass(rendering.render(arg0), rendering.render(in));
													}
												}
											}
										}

									}

								} else {
									// INCOMPLETENESS
									if (!error && show) {
										error = true;
										System.out.print("<p style=\"color:red\">"
												+ "Unsuccessful type validity checking. The property cannot be proved. "
												+ "Not enough information for: " + "</p>");
										System.out.print("<p>" + dp.getIRI().toString().split("#")[1] + "</p>");
									}
								}
							}
						} else {
							// INCOMPLETENESS
							if (!error && show) {
								error = true;
								System.out.print("<p style=\"color:red\">"
										+ "Unsuccessful type validity checking. The property cannot be proved. "
										+ "Not enough information for: " + "</p>");
								System.out.println("<p>" + var_name + "</p>");
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLDataMinCardinality arg0) {
				if (!error & show) {
					System.out.println("<p style=\"color:magenta\">"
							+ "This type cannot be proved by type validity analysis:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
					error = true;
				}
			}

			@Override
			public void visit(OWLDataExactCardinality arg0) {
				if (!error & show) {
					System.out.println("<p style=\"color:magenta\">"
							+ "This type cannot be proved by type validity analysis:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
					error = true;
				}
			}

			@Override
			public void visit(OWLDataMaxCardinality arg0) {
				if (!error & show) {
					System.out.println("<p style=\"color:magenta\">"
							+ "This type cannot be proved by type validity analysis:" + "</p>");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println("<p>" + rendering.render(arg0) + "</p>");
					error = true;
				}
			}

		};

		if (!wrong_analysis) {
			ce.accept(cv);
		}

	}

	public void copy(String file) {
		FileInputStream source = null;
		FileOutputStream dest = null;
		try {
			source = new FileInputStream(file);
		} catch (FileNotFoundException e) {
			System.out.println(e.getMessage());
		}
		try {
			dest = new FileOutputStream("tmp.owl");
		} catch (FileNotFoundException e) {
			System.out.println(e.getMessage());
		}
		byte[] buffer = new byte[1024];
		int length;
		try {
			while ((length = source.read(buffer)) > 0) {
				dest.write(buffer, 0, length);
			}
		} catch (IOException e) {
			System.out.println(e.getMessage());
		}

	};

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

	public static void main(String[] args) {

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
				+ "FILTER (?AGE2 > 0) .\r\n" + "FILTER (?AGE2 < 50) .\r\n" + "FILTER (?AGE > 100) .\r\n"
				+ "BIND((?AGE + ?AGE2) AS ?SUM) .\r\n" + "FILTER (?SUM < 10)\r\n" + "}";

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
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:creates ?MESSAGE \r\n" + "}";

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

		String socex42 = "# ?USER : sn:FriendOfInfluencer\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:friend_of ?USER2 .\r\n"
				+ "?USER2 sn:dailyLikes ?DL .\r\n" + "FILTER (?DL > 50) \r\n" + "}";

		String socex43 = "# ?USER : sn:FriendOfActive\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DA \r\n" + "WHERE \r\n" + "{\r\n" + "?USER sn:friend_of ?USER2 .\r\n"
				+ "?USER2 sn:dailyActivity ?DA .\r\n" + "FILTER (?DA > 50) \r\n" + "}";

		String peoplex1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?A WHERE {?A rdf:type pp:animal . ?A pp:part_of ?plant . ?plant rdf:type pp:plant}\r\n" + "";

		String peoplex2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?L WHERE {?L rdf:type pp:old_lady . ?L pp:has_pet ?P . ?P rdf:type pp:dog}\r\n" + "";

		String peoplex3 = "# ?D : driver\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?D WHERE  {?D rdf:type pp:person}\r\n" + "";

		String peoplex4 = "# ?W : old_lady\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?W WHERE  {?W rdf:type pp:woman}\r\n";

		String peoplex5 = "# ?P : dog_liker\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person . ?P pp:has_pet ?A}\r\n";

		String peoplex6 = "# ?P:grownup\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person}\r\n";

		String peoplex7 = "# ?P:old_lady\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:elderly . ?P pp:has_pet ?A . ?A rdf:type pp:animal}\r\n" + "";

		String peoplex8 = "# ?P:vegetarian\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pp: <http://owl.man.ac.uk/2006/07/sssw/people#>\r\n"
				+ "SELECT ?P WHERE  {?P rdf:type pp:person}\r\n" + "";

		String pizz1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:VegetarianPizza .  ?P pi:hasTopping ?T . ?T rdf:type pi:MeatTopping }\r\n"
				+ "";

		String pizz2 = "# ?P:RealItalianPizza\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P pi:hasTopping ?T . ?T rdf:type pi:FruitTopping }\r\n" + "";

		String pizz3 = "# ?P:ThinAndCrispyPizza\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:MeatyPizza .  ?P pi:hasTopping ?T . ?T rdf:type pi:FruitTopping }\r\n" + "";

		String pizz4 = "# ?P:CheeseyPizza\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX pi: <http://www.co-ode.org/ontologies/pizza/pizza.owl#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P rdf:type pi:Pizza . ?P pi:hasTopping ?T. ?T rdf:type pi:CheeseTopping }\r\n" + "";

		String c1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E rdf:type co:failed . ?E co:scores ?V . FILTER (?V > 5)}";

		String c2 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E co:scores 3}";

		String c3 = "# ?E: finished\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S co:is_enrolled ?E . ?E co:scores ?Z . FILTER(?Z <3)}";

		String c4 = "# ?S: student\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S \r\n"
				+ "WHERE { ?S rdf:type co:person }";

		String c5 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S co:is_enrolled ?E . ?E co:scores ?V }";

		String c6 = "# ?E: passed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S co:is_enrolled ?E . ?E co:scores ?V . FILTER (?V >= 3) }";

		String c7 = "# ?E: failed\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX co: <http://www.semanticweb.org/course#>\r\n" + "SELECT ?S ?E\r\n"
				+ "WHERE { ?S rdf:type co:student . ?S co:is_enrolled ?E . ?E co:scores ?V . FILTER (?V >= 3) }";

		String con1 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P \r\n"
				+ "WHERE { ?P rdf:type con:acceptance . ?P con:has_review ?R . ?R con:score ?V . FILTER (?V < 1)  }";

		String con2 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A \r\n"
				+ "WHERE { ?A rdf:type con:acceptance . ?A con:submits ?P . ?P rdf:type con:rejection  }";

		String con3 = "# ?P : acceptance\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P \r\n"
				+ "WHERE { ?A con:submits ?P  }";

		String con4 = "# ?P : acceptance\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P con:has_review ?R  }";

		String con5 = "# ?P : acceptance\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P rdf:type con:paper  }";

		String con6 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P rdf:type con:paper  }";

		String con7 = "# ?P: acceptance \r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?A ?P\r\n"
				+ "WHERE { ?A con:submits ?P . ?P con:has_review ?R. ?R rdf:type con:accepted  }";

		String con8 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P con:has_review ?R . ?R rdf:type con:rejected }";

		String con9 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P con:has_review ?R . ?R con:score ?V . FILTER (?V > 0) }";

		String con10 = "# ?P : rejection\r\n" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\r\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\r\n"
				+ "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\r\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\r\n"
				+ "PREFIX con: <http://www.semanticweb.org/conference#>\r\n" + "SELECT ?P\r\n"
				+ "WHERE { ?P con:has_review ?R }";

		OWLOntologyManager manager;
		OWLOntologyManager manager_rdf;
		OWLOntologyManager manager_owl;
		OWLOntology ontology;
		OWLOntology ont_rdf;
		OWLOntology ont_owl;
		OWLDataFactory dataFactory;
		OWLDataFactory df_rdf;
		OWLDataFactory df_owl;
		String file = "C:/course.owl";
		String rdf = "C:/rdf-vocabulary.owl";
		String owl = "C:/owl-vocabulary.owl";

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

		long startTime = System.currentTimeMillis();

		TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory, df_rdf,
				df_owl, file);

		/*
		 * try { t.SPARQL_CORRECTNESS(socex32); } catch (Exception e) { // TODO
		 * Auto-generated catch block e.printStackTrace(); }
		 */

		try {
			t.SPARQL_TYPE_VALIDITY(c2, "E", "http://www.semanticweb.org/course#passed");
		} catch (Exception e) {
			// TODO Auto-generated catch block e.printStackTrace(); }
		}

		long estimatedTime = System.currentTimeMillis() - startTime;
		System.out.println("");
		System.out.println("Analysis done in " + estimatedTime + " ms");

	};

}
