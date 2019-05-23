package CTSPARQL;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.text.DateFormat;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Locale;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;

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
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLDatatypeRestriction;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLFacetRestriction;
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
import com.hp.hpl.jena.sparql.engine.Rename;
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

import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;

public class TSPARQL {

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
	Boolean wrong_analysis;
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
					result = result + rendering.render(ax) + "\n";
				}
			} catch (OWLRuntimeException ex) {
				System.out.println("cannot explain: " + ex.getMessage());
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
				result = result + rendering.render(ax) + "\n";
			}
		} catch (OWLRuntimeException ex) {
			System.out.println("cannot explain: " + ex.getMessage());
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
			System.out.println("Inconsistent query, please check consistency.");
			wrong_analysis = true;
		}
		return result;
	}

	private void printClass(Object class_name, Object individual_name) {
		System.out.println(individual_name + " Type " + class_name);
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

	public Boolean Existence(TriplePath tp) {
		Boolean result = true;
		if (tp.getSubject().isURI() && !isDeclared(tp.getSubject().getNameSpace(), tp.getSubject().getLocalName())
				&& !wrong_analysis) {
			System.out.print("This item is not declared by the ontology: ");
			System.out.println(tp.getSubject().getLocalName());
			result = false;
			wrong_analysis = true;
		}
		if (tp.getPredicate().isURI() && !isDeclared(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
				&& !wrong_analysis) {
			System.out.print("This item is not declared by the ontology: ");
			System.out.println(tp.getPredicate().getLocalName());
			result = false;
			wrong_analysis = true;
		}
		if (tp.getObject().isURI() && !isDeclared(tp.getObject().getNameSpace(), tp.getObject().getLocalName())
				&& !wrong_analysis) {
			System.out.print("This item is not declared by the ontology: ");
			System.out.println(tp.getObject().getLocalName());
			result = false;
			wrong_analysis = true;
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
						System.out.println("Literal cannot be used as subject:");
						System.out.println(tp);
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
								System.out.println(e.getMessage());
							}
						} else {
							System.out.println("Literal used with an object property:");
							System.out.println(tp);
							wrong_analysis = true;
						}
					} else /* VUL */
					{

						// ADD TYPE
						OWLNamedIndividual ni = null;
						ni = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
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
						OWLNamedIndividual ni2 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						if (isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
							OWLDataProperty o = dft.getOWLDataProperty(
									IRI.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
							OWLLiteral owlTypedLiteral = dft.getOWLLiteral(tp.getObject().getLiteralValue().toString(),
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
							System.out.println("Literal used with an object property:");
							System.out.println(tp);
							wrong_analysis = true;
						}
					}
				} else if (tp.getPredicate().isVariable()) {
					/* second V should be a data property */
					if (tp.getSubject().isVariable()) /* VVL */ {

						// ADD TYPE
						OWLNamedIndividual ni1 = null;
						ni1 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						OWLClass cls1 = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
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
						OWLClass cls2 = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
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
							System.out.println("Literal cannot be used as subject:");
							System.out.println(tp);
							wrong_analysis = true;
						}
					}
				} else /*-LL*/
				{
					System.out.println("Literal cannot be used as property:");
					System.out.println(tp);
					wrong_analysis = true;
				}
			} else if (tp.getObject().isURI()) {
				if (tp.getSubject().isLiteral()) /* L-U */ {
					System.out.println("Literal cannot be used as subject:");
					System.out.println(tp);
					wrong_analysis = true;
				} else {
					if (tp.getSubject().isVariable()) {
						if (tp.getPredicate().isLiteral()) /* VLU */ {
							System.out.println("Literal cannot be used as property:");
							System.out.println(tp);
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
								OWLObjectProperty o = dft.getOWLObjectProperty(IRI
										.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
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
									System.out.println("Class or Individual used as data property:");
									System.out.println(tp);
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
								System.out.println("Literal cannot be used as subject:");
								System.out.println(tp);
								wrong_analysis = true;
							}
						}
					} else {
						if (tp.getPredicate().isLiteral()) /* ULU */
						{
							System.out.println("Literal cannot be a property:");
							System.out.println(tp);
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
								OWLObjectProperty o = dft.getOWLObjectProperty(IRI
										.create(tp.getPredicate().getNameSpace() + tp.getPredicate().getLocalName()));
								OWLAxiom axiom = dft.getOWLObjectPropertyAssertionAxiom(o, ni3, ni4);
								AddAxiom addAxiom = new AddAxiom(ont, axiom);
								mng.applyChange(addAxiom);
								try {
									mng.saveOntology(ont);
								} catch (OWLOntologyStorageException e) {
									System.out.println(e.getMessage());
								}
							} else {
								System.out.println("Individual used with a data property:");
								System.out.println(tp);
								wrong_analysis = true;
							}
						}
					}
				}
			}

			else if (tp.getSubject().isLiteral()) /* L-V */ {
				System.out.println("Literal cannot be used as subject:");
				System.out.println(tp);
				wrong_analysis = true;
			} else if (tp.getSubject().isVariable()) {
				if (tp.getPredicate().isLiteral()) /* VLV */
				{
					System.out.println("Literal cannot be a predicate:");
					System.out.println(tp);
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
						ni1 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						OWLClass cls1 = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls1, ni1);
						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
						mng.applyChange(addAxiom1);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							System.out.println(e.getMessage());
						}
						OWLNamedIndividual ni2 = null;
						ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
						ni3 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
					} else if (isObjectPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
							&& !isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {

						// ADD TYPE
						OWLNamedIndividual ni1 = null;
						ni1 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						OWLClass cls1 = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls1, ni1);
						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
						mng.applyChange(addAxiom1);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							System.out.println(e.getMessage());
						}
						OWLNamedIndividual ni2 = null;
						ni2 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
						OWLClass cls2 = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
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
						ni3 = dft
								.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
						OWLNamedIndividual ni4 = null;
						ni4 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
							System.out.println("Class or Individual used as property:");
							System.out.println(tp);
						}
					}

				} else /* VVV */
				{

					// ADD TYPE
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
						System.out.println(e.getMessage());
					}
				}
			} else {
				if (tp.getPredicate().isLiteral()) /* ULV */ {
					System.out.println("Literal cannot be a predicate:");
					System.out.println(tp);
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
						ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
								System.out.println(e.getMessage());
							}
							addTypeVariable(tp.getObject().getName().substring(0).toUpperCase(),
									"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
							types_literals.put(tp.getObject().getName(),
									"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
						}
					} else if (isObjectPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())
							&& !isDataPropertyAll(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {

						// ADD TYPE
						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
						ni3 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
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
							System.out.println("Class or Individual used as property:");
							System.out.println(tp);
						}
					}
				} else /* UVV */
				{
					// ADD TYPE
					OWLNamedIndividual ni = null;
					ni = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getPredicate().getName().substring(0)));
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
	};

	public List<List<String>> SPARQL_ANALYSIS(String file, String queryString, Integer step) {

		Set<OWLAxiom> axs = ontology.getABoxAxioms(true);
		for (OWLAxiom ax : axs) {
			if (!ax.isOfType(AxiomType.CLASS_ASSERTION)) {
				manager.removeAxiom(ontology, ax);
			}
		}
		try {
			manager.saveOntology(ontology);
		} catch (OWLOntologyStorageException e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
		}
		OWLClass lit = dataFactory.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
		OWLClass res = dataFactory.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));

		/*
		 * Set<OWLNamedIndividual> individuals = ontology.getIndividualsInSignature();
		 * for (OWLNamedIndividual i: individuals) { for (OWLNamedIndividual i2:
		 * individuals) { if (! i.equals(i2)) { OWLDifferentIndividualsAxiom ax =
		 * dataFactory.getOWLDifferentIndividualsAxiom(i2); AddAxiom addAxiom = new
		 * AddAxiom(ontology, ax); manager.applyChange(addAxiom); } } }
		 * 
		 * try { manager.saveOntology(ontology); } catch (OWLOntologyStorageException e)
		 * { // TODO Auto-generated catch block System.out.println(e.getMessage()); }
		 */

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
			System.out.println("SPARQL expression not supported:");
			System.out.println(query);
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
				if (tp.getSubject().isVariable()) {
					Set<OWLClassExpression> typ = ClassOfVariable(
							IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
					datatriples.add(tp);
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
				System.out.println("SPARQL expression not supported:");
				System.out.println(ex);
				wrong_analysis = true;
				rules.clear();
			}
			String urio = ontology.getOntologyID().getOntologyIRI().toString();
			for (TriplePath tp : ctriples) {
				Set<OWLClassExpression> typ = ClassOfVariable(
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
				datatriples.add(tp);
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
		} else if (el.getExpr().getFunction().getFunctionName(null) == "notexists") {
			System.out.println("SPARQL expression not supported:");
			System.out.println(el);
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
			constraints_elements.add(el.getExpr().toString());
			List<String> ss = new ArrayList<>(SExprtoPTerm(el.getExpr(), null));
			for (int i = 0; i < ss.size(); i++) {
				rules.get(current).add(ss.get(i));
			}
		} else {
			wrong_analysis = true;
			System.out.println("Expression " + el.getExpr().getFunction().getFunctionName(null)
					+ " not allowed in FILTER expression.");
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

		System.out.println("SPARQL expression not supported:");
		System.out.println(el);
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
				System.out.println("SPARQL expression not supported:");
				System.out.println(e);
				wrong_analysis = true;
				rules.clear();
			}
		}
	}

	public void elementMinus(ElementMinus el, Integer step, String fileo) {
		System.out.println("SPARQL expression not supported:");
		System.out.println(el);
		wrong_analysis = true;
		rules.clear();
	}

	public void elementOptional(ElementOptional el, Integer step, String fileo) {
		System.out.println("SPARQL expression not supported:");
		System.out.println(el);
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
			System.out.println("SPARQL expression not supported:");
			System.out.println(query);
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
			System.out.println("SPARQL expression not supported:");
			System.out.println(e);
			wrong_analysis = true;
			rules.clear();
		}
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		for (TriplePath tp : ctriples) {
			Set<OWLClassExpression> typ = ClassOfVariable(
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
			datatriples.add(tp);
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
				if (!wrong_analysis) {
					System.out.println("This type is not supported by consistency analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					wrong_analysis = true;
				}

			}

			@Override
			public void visit(OWLObjectComplementOf arg0) {
				if (!wrong_analysis) {
					System.out.println("This type is not supported by consistency analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					wrong_analysis = true;
				}

			}

			@Override
			public void visit(OWLObjectSomeValuesFrom arg0) {
			}

			@Override
			public void visit(OWLObjectAllValuesFrom arg0) {
				if (ctriplesn.containsKey(var_name)) {
					OWLObjectAllValuesFrom allValuesFrom = (OWLObjectAllValuesFrom) arg0;
					OWLClassExpression filler = allValuesFrom.getFiller();
					for (OWLObjectProperty dp : allValuesFrom.getObjectPropertiesInSignature()) {
						Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
							Set<Node> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
							for (Node var : vars_) {
								OWLRestriction(filler.asOWLClass(), var);
							}
						}
					}
				}
			}

			@Override
			public void visit(OWLObjectHasValue arg0) {
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
				if (ctriplesn.containsKey(var_name)) {
					OWLDataAllValuesFrom allValuesFrom = (OWLDataAllValuesFrom) arg0;
					OWLDataRange filler = allValuesFrom.getFiller();
					for (OWLDataProperty dp : allValuesFrom.getDataPropertiesInSignature()) {
						Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
							Set<Node> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
							String cons = "";
							for (Node var : vars_) {
								OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;
								if (r.getDatatype().isInteger()) {
									for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
										if (fr.getFacet().toString() == "maxExclusive") {
											if (var.isVariable()) {
												cons = cons + var.toString().substring(1).toUpperCase() + "#<"
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " < "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + var.getLiteralValue().toString() + "#<"
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.getLiteralValue().toString() + " < "
														+ fr.getFacetValue().getLiteral() + " )");
											}

										} else if (fr.getFacet().toString() == "maxInclusive") {
											if (var.isVariable()) {
												cons = cons + var.toString().substring(1).toUpperCase() + "#<="
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " <= "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + var.getLiteralValue().toString() + "#<="
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.getLiteralValue().toString()
														+ " <= " + fr.getFacetValue().getLiteral() + " )");
											}
										} else if (fr.getFacet().toString() == "minExclusive") {
											if (var.isVariable()) {
												cons = cons + var.toString().substring(1).toUpperCase() + "#>"
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " > "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + var.getLiteralValue().toString() + "#>"
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.getLiteralValue().toString() + " > "
														+ fr.getFacetValue().getLiteral() + " )");
											}
										} else if (fr.getFacet().toString() == "minInclusive") {
											if (var.isVariable()) {
												cons = cons + var.toString().substring(1).toUpperCase() + "#>="
														+ fr.getFacetValue().getLiteral() + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " >= "
														+ fr.getFacetValue().getLiteral() + " )");
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
												cons = cons + "{" + var.toString().substring(1).toUpperCase() + "<"
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " < "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + "{" + var.getLiteralValue().toString() + "<"
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.getLiteralValue().toString() + " < "
														+ fr.getFacetValue().getLiteral() + " )");
											}
										} else if (fr.getFacet().toString() == "maxInclusive") {
											if (var.isVariable()) {
												cons = cons + "{" + var.toString().substring(1).toUpperCase() + "<="
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " <= "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + "{" + var.getLiteralValue().toString() + "<="
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("(" + var.getLiteralValue().toString() + " <= "
														+ fr.getFacetValue().getLiteral() + ")");
											}
										} else if (fr.getFacet().toString() == "minExclusive") {
											if (var.isVariable()) {
												cons = cons + "{" + var.toString().substring(1).toUpperCase() + ">"
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " > "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + "{" + var.getLiteralValue().toString() + ">"
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.getLiteralValue().toString() + " > "
														+ fr.getFacetValue().getLiteral() + " )");
											}
										} else if (fr.getFacet().toString() == "minInclusive") {
											if (var.isVariable()) {
												cons = cons + "{" + var.toString().substring(1).toUpperCase() + ">="
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.toString().toUpperCase() + " >= "
														+ fr.getFacetValue().getLiteral() + " )");
											} else {
												cons = cons + "{" + var.getLiteralValue().toString() + ">="
														+ fr.getFacetValue().getLiteral() + "}" + ",";
												constraints_elements.add("( " + var.getLiteralValue().toString()
														+ " >= " + fr.getFacetValue().getLiteral() + " )");
											}
										}
									}
								} else {
									if (!wrong_analysis) {
										wrong_analysis = true;
										System.out.println("OWL Restriction not allowed:");
										ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
										System.out.println(rendering.render(arg0));
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

			@Override
			public void visit(OWLDataSomeValuesFrom arg0) {
			}

			@Override
			public void visit(OWLDataHasValue arg0) {
				if (ctriplesn.containsKey(var_name)) {
					OWLDataHasValue HasValue = (OWLDataHasValue) arg0;
					OWLLiteral value = HasValue.getValue();
					for (OWLDataProperty dp : HasValue.getDataPropertiesInSignature()) {
						Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
							Set<Node> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
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
									if (!wrong_analysis) {
										wrong_analysis = true;
										System.out.println("OWL Restriction not allowed:");
										ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
										System.out.println(rendering.render(arg0));
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

			@Override
			public void visit(OWLDataMinCardinality arg0) {
			}

			@Override
			public void visit(OWLDataExactCardinality arg0) {
			}

			@Override
			public void visit(OWLDataMaxCardinality arg0) {
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
							System.out.print("The following variable is not typed: ");
							System.out.println(v);
							wrong_analysis = true;
						}
					}
				} else {
					if (!wrong_analysis) {
						System.out.print("The following variable is not typed: ");
						System.out.println(v);
						wrong_analysis = true;
					}
				}
			} else {
				if (!wrong_analysis) {
					System.out.print("The following variable is not typed: ");
					System.out.println(sv);
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
				pt.add(result + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else if ((isInteger(st.toString()) || (isReal(st.toString())))) {
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:float");
				pt.add(st.toString() + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
			} else {
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:string");
				int MAX_LENGTH = 13;
				long result = 0;
				for (int i = 0; i < st.toString().length(); i++)
					result += pow(27, MAX_LENGTH - i - 1) * (1 + st.toString().charAt(i));
				pt.add(result + "=" + var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase());
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
				} else {
				}

				if (types_literals.containsKey("B" + act)) {
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
						pt.add("W" + act + " #= " + "U" + act + st.getFunction().getOpName() + "V" + act);
					} else if (types_literals.get("W" + act).equals("http://www.types.org#xsd:positiveInteger")) {
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
				} else {
				}
				String res = var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase();
				types_literals.put(res, types_literals.get("W" + act));
				if (types_literals.containsKey(res)) {
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
					} else if (types_literals.get(res).equals("http://www.types.org#xsd:float")
							|| types_literals.get(res).equals("http://www.types.org#xsd:double")
							|| types_literals.get(res).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + res + " =:=" + "W" + act + " }");
					} else {
						if (!wrong_analysis) {
							System.out.print("The following variable is not typed: ");
							System.out.println(res);
							wrong_analysis = true;
						}
					}
				} else {
					if (!wrong_analysis) {
						System.out.print("The following variable is not typed: ");
						System.out.println(res);
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
			System.out.print("The following variable is not typed: ");
			System.out.println(variable);
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
					System.out.println("Successful correctness checking.");
				} else {
					System.out.println("Unsuccessful correctness checking due to:");
					System.out.print(r);
				}
			} else {
				System.out.println("Unsuccessful correctness checking due to:");
				System.out.print(r);
				for (List<String> rule : rules) {
					for (int i = 1; i < rule.size(); i++) {
						System.out.println(rule.get(i).replace("#", ""));
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
		owl_type_validity(ce, in, Node.createVariable(var_name));
		if (!error && !wrong_analysis) {
			System.out.println("Successful type validity checking. The property has been proved.");
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
					addTypeAssertion(arg0, in);
					OWLClass res = dataFactory.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Resource"));
					addTypeAssertion(res, in);
					String consistency = consistency();
					if (consistency == "true") {
					} else {
						error = true;
						System.out.println(
								"Unsuccessful type validity checking. Case 1.\n Caused by the following inconsistency:");
						System.out.print(explanations());

					}
					removeTypeAssertion(arg0, in);
					Set<OWLClassExpression> ec = arg0.getEquivalentClasses(ontology);
					for (OWLClassExpression e : ec) {
						if (!error) {
							e.accept(this);
						}
					}
					Set<OWLClassExpression> sc = arg0.getSuperClasses(ontology);
					for (OWLClassExpression e : sc) {
						if (!error) {
							e.accept(this);
						}
					}
					if (consistency == "true" && !error) {

						error = true;
						System.out.println(
								"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						printClass(rendering.render(arg0), rendering.render(in));
					}
				}
			}

			@Override
			public void visit(OWLObjectIntersectionOf arg0) {
				Set<OWLClassExpression> ec = arg0.getOperands();
				for (OWLClassExpression e : ec) {
					if (!error) {
						e.accept(this);
					}
				}
			}

			@Override
			public void visit(OWLObjectUnionOf arg0) {

				if (!error) {
					System.out.println("This type is not supported by type validity analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLObjectComplementOf arg0) {
				if (!error) {
					System.out.println("This type is not supported by type validity analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLObjectSomeValuesFrom arg0) {
				if (ctriplesn.containsKey(var_name)) {
					OWLObjectSomeValuesFrom someValuesFrom = (OWLObjectSomeValuesFrom) arg0;
					OWLClassExpression filler = someValuesFrom.getFiller();

					for (OWLObjectProperty dp : someValuesFrom.getObjectPropertiesInSignature()) {
						Map<Node, Set<Node>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
							Set<Node> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
							for (Node var : vars_) {
								String urio = ontology.getOntologyID().getOntologyIRI().toString();
								OWLNamedIndividual in = dataFactory.getOWLNamedIndividual(IRI.create(urio + '#' + var));
								owl_type_validity(filler.asOWLClass(), in, var);
							}
						}
					}
				}

				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						System.out.println(
								"Unsuccessful type validity checking. Case 2.\n The following class membership cannot be proved:");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						printClass(rendering.render(arg0), rendering.render(in));
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						} else {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 2.1.\n Caused by the following inconsistency:");
							System.out.print(explanations());
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectAllValuesFrom arg0) {
				if (!error) {
					System.out.println("This type cannot be proved by type validity analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLObjectHasValue arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						System.out.println(
								"Unsuccessful type validity checking. Case 3.\n The following class membership cannot be proved:");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						printClass(rendering.render(arg0), rendering.render(in));
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						} else {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 3.1.\n Caused by the following inconsistency:");
							System.out.print(explanations());
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectMinCardinality arg0) {
			}

			@Override
			public void visit(OWLObjectExactCardinality arg0) {
				if (!error) {
					System.out.println("This type cannot be proved by type validity analysis:");

					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLObjectMaxCardinality arg0) {
				if (!error) {
					System.out.println("This type cannot be proved by type validity analysis:");

					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLObjectHasSelf arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						System.out.println(
								"Unsuccessful type validity checking. Case 4.\n The following class membership cannot be proved:");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						printClass(rendering.render(arg0), rendering.render(in));
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						} else {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 4.1.\n Caused by the following inconsistency:");
							System.out.print(explanations());
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectOneOf arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						System.out.println(
								"Unsuccessful type validity checking. Case 5.\n The following class membership cannot be proved:");
						ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
						printClass(rendering.render(arg0), rendering.render(in));
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						} else {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 5.1.\n Caused by the following inconsistency:");
							System.out.print(explanations());
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLDataAllValuesFrom arg0) {
				if (!error) {
					System.out.println("This type cannot be proved by type validity analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLDataSomeValuesFrom arg0) {
				if (!error) {
					if (arg0.isObjectRestriction()) {
						OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
						String entailment = entailment(axiom);
						if (entailment == "false") {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 6.\n The following class membership cannot be proved:");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						} else {
							addTypeAssertion(arg0, in);
							String consistency = consistency();
							if (consistency == "true") {
								error = true;
								System.out.println(
										"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							} else {
								error = true;
								System.out.println(
										"Unsuccessful type validity checking. Case 6.1.\n Caused by the following inconsistency:");
								System.out.print(explanations());

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
								if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
									Set<Node> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
									String cons = "";
									for (Node var : vars_) {
										OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;
										if (r.getDatatype().isInteger()) { // CHANGED , by ;
											for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
												if (fr.getFacet().toString() == "maxExclusive") {
													if (var.isVariable()) {
														cons = cons + "#\\" + var.toString().substring(1).toUpperCase()
																+ "#<" + fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "#\\" + var.getLiteralValue().toString() + "#<"
																+ fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "maxInclusive") {
													if (var.isVariable()) {
														cons = cons + "#\\" + var.toString().substring(1).toUpperCase()
																+ "#<=" + fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " <= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "#\\" + var.getLiteralValue().toString() + "#<="
																+ fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " <= " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minExclusive") {
													if (var.isVariable()) {
														cons = cons + "#\\" + var.toString().substring(1).toUpperCase()
																+ "#>" + fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "#\\" + var.getLiteralValue().toString() + "#>"
																+ fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minInclusive") {
													if (var.isVariable()) {
														cons = cons + "#\\" + var.toString().substring(1).toUpperCase()
																+ "#>=" + fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "#\\" + var.getLiteralValue().toString() + "#>="
																+ fr.getFacetValue().getLiteral() + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " >= " + fr.getFacetValue().getLiteral() + ")");
													}
												}
											}
										} else if (r.getDatatype().isDouble() // CHANGED , by ;
												|| r.getDatatype().isFloat()) {
											for (OWLFacetRestriction fr : r.getFacetRestrictions()) {

												if (fr.getFacet().toString() == "maxExclusive") {

													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ ">=" + fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + ">="
																+ fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " >= " + fr.getFacetValue().getLiteral() + " )");
													}

												} else if (fr.getFacet().toString() == "maxInclusive") {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ ">" + fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + ">"
																+ fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " > " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minExclusive") {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ "=<" + fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " =< " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + "=<"
																+ fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " =< " + fr.getFacetValue().getLiteral() + " )");
													}
												} else if (fr.getFacet().toString() == "minInclusive") {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ "<" + fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.toString().toUpperCase()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													} else {
														cons = cons + "{" + var.getLiteralValue().toString() + "<"
																+ fr.getFacetValue().getLiteral() + "}" + ";";
														constraints_elements.add("( " + var.getLiteralValue().toString()
																+ " < " + fr.getFacetValue().getLiteral() + " )");
													}
												}
											}
										} else {
											if (!error) {
												error = true;
												System.out.println("OWL Restriction not allowed:");
												ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
												System.out.println(rendering.render(arg0));
											}
										}
									}
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

									if (!cons.isEmpty()) {
										cons = cons.substring(0, cons.length() - 1);
									}

									String newhead = "";
									for (int i = 1; i < rules.get(0).size(); i++) {
										newhead = newhead + rules.get(0).get(i) + ',';
									}

									if (!newhead.isEmpty()) {
										newhead = newhead.substring(0, newhead.length() - 1);
										String head;
										head = newhead + "," + cons + "," + domain;
										org.jpl7.Query qimpl = new org.jpl7.Query(head);
										if (qimpl.hasSolution())
										// COUNTEREXAMPLE
										{
											error = true;
											System.out.println(
													"Unsuccessful type validity checking. Case 7. Counterexample:");
											Map<String, Term>[] sols = qimpl.allSolutions();
											for (Map<String, Term> s : sols) {
												for (String key : s.keySet())
													if (s.get(key).isCompound()) {
														System.out.println(rename.get(key) + "=" + s.get(key));
													}
											}
										} else {
											cons = "";
											for (Node var : vars_) {
												OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;
												if (r.getDatatype().isInteger()) { // CHANGED ; by ,
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
																		+ "#<=" + fr.getFacetValue().getLiteral() + ",";
															} else {
																cons = cons + var.getLiteralValue().toString() + "#<="
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
												} else if (r.getDatatype().isFloat() || // CHANGED ; by ,
												r.getDatatype().isDouble()) {
													for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
														if (fr.getFacet().toString() == "maxExclusive") {
															if (var.isVariable()) {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ "<" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															} else {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ "<" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															}
														} else if (fr.getFacet().toString() == "maxInclusive") {
															if (var.isVariable()) {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ "<=" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															} else {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ "<=" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															}
														} else if (fr.getFacet().toString() == "minExclusive") {
															if (var.isVariable()) {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ ">" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															} else {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ ">" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															}
														} else if (fr.getFacet().toString() == "minInclusive") {
															if (var.isVariable()) {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ ">=" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															} else {
																cons = cons + "{"
																		+ var.toString().substring(1).toUpperCase()
																		+ ">=" + fr.getFacetValue().getLiteral() + "}"
																		+ ",";
															}
														}
													}
												} else {
													if (!error) {
														error = true;
														System.out.println("OWL Restriction not allowed:");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														System.out.println(rendering.render(arg0));
													}
												}
											}
											if (!cons.isEmpty()) {
												cons = cons.substring(0, cons.length() - 1);
											}
											newhead = "";
											for (int i = 1; i < rules.get(0).size(); i++) {
												newhead = newhead + rules.get(0).get(i) + ',';
											}
											if (!newhead.isEmpty()) {
												newhead = newhead.substring(0, newhead.length() - 1);

												head = newhead + "," + cons + "," + domain;
												org.jpl7.Query qcons = new org.jpl7.Query(head);
												if (!qcons.hasSolution()) {
													// INCONSISTENCY
													error = true;
													System.out.println(
															"Unsuccessful type validity checking. Case 7.1.\n Caused by the following inconsistency:");
													System.out.println(head);
												} else {
													// ENTAILMENT
													head = newhead + "->" + cons;
													qcons = new org.jpl7.Query(head);
													if (qcons.hasSolution()) {
													} else {
														error = true;
														System.out.println(
																"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														printClass(rendering.render(arg0), rendering.render(in));
													}
												}
											} else {
												// INCOMPLETENESS
												error = true;
												System.out.println(
														"Unsuccessful type validity checking. Case 7.2.\n The following expression cannot be proved:");
												System.out.println(head);
											}
										}
									} else {
										// INCOMPLETENESS
										error = true;
										System.out.println(
												"Unsuccessful type validity checking. Case 7.3.\n The following expression cannot be proved:");
										for (String c : constraints_elements) {
											System.out.print(c.replace("?", ""));
										}
										System.out.println("");
									}
								} else {
									// INCOMPLETENESS
									error = true;
									System.out.print(
											"Unsuccessful type validity checking. Case 7.4.\n The property cannot be proved.\n "
													+ "Not enough information for: ");
									System.out.println(dp.getIRI().toString().split("#")[1]);
								}
							}
						} else {
							// INCOMPLETENESS
							error = true;
							System.out.print(
									"Unsuccessful type validity checking. Case 7.5 . The property cannot be proved. "
											+ "Not enough information for: ");
							System.out.println(var_name);
						}
					}
				}
			}

			@Override
			public void visit(OWLDataHasValue arg0) {
				if (!error) {
					if (arg0.isObjectRestriction()) {
						OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
						String entailment = entailment(axiom);
						if (entailment == "false") {
							error = true;
							System.out.println(
									"Unsuccessful type validity checking. Case 8.\n The following class membership cannot be proved:");
							ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
							printClass(rendering.render(arg0), rendering.render(in));
						} else {
							addTypeAssertion(arg0, in);
							String consistency = consistency();
							if (consistency == "true") {
								error = true;
								System.out.println(
										"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
								ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
								printClass(rendering.render(arg0), rendering.render(in));
							} else {
								error = true;
								System.out.println(
										"Unsuccessful type validity checking. Case 8.1.\n Caused by the following inconsistency:");
								System.out.print(explanations());
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
								if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
									String cons = "";
									Set<Node> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
									for (Node var : vars_) {
										if (val.isInteger()) {
											if (var.isVariable()) {
												cons = cons + "#\\" + var.toString().substring(1).toUpperCase() + "#="
														+ val.getLiteral();
												constraints_elements.add("(" + var.toString().toUpperCase() + "="
														+ val.getLiteral() + ")");
											} else {
												cons = cons + "#\\" + var.getLiteralValue().toString() + "#="
														+ val.getLiteral();
												constraints_elements.add("(" + var.getLiteralValue().toString() + "="
														+ val.getLiteral() + ")");
											}
										} else if (val.isFloat() || val.isDouble()) {
											if (var.isVariable()) {
												cons = cons + "#\\" + var.toString().substring(1).toUpperCase() + "=\\="
														+ val.getLiteral();
												constraints_elements.add("(" + var.toString().toUpperCase() + "="
														+ val.getLiteral() + ")");
											} else {
												cons = cons + "#\\" + var.getLiteralValue().toString() + "=\\="
														+ val.getLiteral();
												constraints_elements.add("(" + var.getLiteralValue().toString() + "="
														+ val.getLiteral() + ")");
											}
										}
									}
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
									String newhead = "";
									for (int i = 1; i < rules.get(0).size(); i++) {
										newhead = newhead + rules.get(0).get(i) + ',';
									}
									if (!newhead.isEmpty()) {
										newhead = newhead.substring(0, newhead.length() - 1);
										String head;
										head = newhead + "," + cons + "," + domain;
										org.jpl7.Query qimpl = new org.jpl7.Query(head);
										if (qimpl.hasSolution()) { // COUNTEREXAMPLE
											error = true;
											System.out.println(
													"Unsuccessful type validity checking. Case 9. Counterexample:");
											Map<String, Term>[] sols = qimpl.allSolutions();
											for (Map<String, Term> s : sols) {
												for (String key : s.keySet())
													if (s.get(key).isCompound()) {
														System.out.println(rename.get(key) + "=" + s.get(key));
													}
											}
										} else {
											vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
											cons = "";
											for (Node var : vars_) {

												if (val.isInteger()) {
													if (var.isVariable()) {
														cons = cons + var.toString().substring(1).toUpperCase() + "#="
																+ val.getLiteral();
													} else {
														cons = cons + var.getLiteral() + "#=" + val.getLiteral();
													}
												} else if (val.isFloat() || val.isDouble()) {
													if (var.isVariable()) {
														cons = cons + "{" + var.toString().substring(1).toUpperCase()
																+ "=:=" + val.getLiteral() + "}";
													} else {
														cons = cons + "{" + var.getLiteral() + "=:=" + val.getLiteral()
																+ "}";
													}
												} else {
													if (!error) {
														error = true;
														System.out.println("OWL Restriction not allowed:");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														System.out.println(rendering.render(arg0));
													}
												}
											}
											newhead = "";
											for (int i = 1; i < rules.get(0).size(); i++) {
												newhead = newhead + rules.get(0).get(i) + ',';
											}
											if (!newhead.isEmpty()) {
												newhead = newhead.substring(0, newhead.length() - 1);
												head = newhead + "," + cons;
												org.jpl7.Query qcons = new org.jpl7.Query(head);
												if (!qcons.hasSolution()) {
													// INCONSISTENCY
													error = true;
													System.out.println(
															"Unsuccessful type validity checking. Case 9.1.\n Caused by the following inconsistency:");
													System.out.println(head);
												} else {
													// ENTAILMENT
													head = newhead + "->" + cons;
													qcons = new org.jpl7.Query(head);
													if (qcons.hasSolution()) {
													} else {
														error = true;
														System.out.println(
																"Unsuccessful type validity checking. Case 10.\n The following class membership cannot be proved:");
														ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
														printClass(rendering.render(arg0), rendering.render(in));
													}
												}
											} else {
												// INCOMPLETENESS
												error = true;
												System.out.println(
														"Unsuccessful type validity checking. Case 9.2.\n The following expression cannot be proved:");
												System.out.println(cons);
											}
										}
									} else {
										// INCOMPLETENESS
										error = true;
										System.out.println(
												"Unsuccessful type validity checking. Case 9.3.\n The following expression cannot be proved:");
										for (String c : constraints_elements) {
											System.out.print(c.replace("?", ""));
										}
										System.out.println("");
									}
								} else {
									// INCOMPLETENESS
									error = true;
									System.out.print(
											"Unsuccessful type validity checking. Case 9.4.\n The property cannot be proved.\n "
													+ "Not enough information for: ");
									System.out.print(dp.getIRI().toString().split("#")[1]);
								}
							}
						} else {
							// INCOMPLETENESS
							error = true;
							System.out.print(
									"Unsuccessful type validity checking. Case 9.5. The property cannot be proved. "
											+ "Not enough information for: ");
							System.out.println(var_name);
						}
					}
				}
			}

			@Override
			public void visit(OWLDataMinCardinality arg0) {
			}

			@Override
			public void visit(OWLDataExactCardinality arg0) {
				if (!error) {
					System.out.println("This type cannot be proved by type validity analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
					error = true;
				}
			}

			@Override
			public void visit(OWLDataMaxCardinality arg0) {
				if (!error) {
					System.out.println("This type cannot be proved by type validity analysis:");
					ManchesterOWLSyntaxOWLObjectRendererImpl rendering = new ManchesterOWLSyntaxOWLObjectRendererImpl();
					System.out.println(rendering.render(arg0));
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

		// CORRECTNESS

		// First Method. Wrongly Typed Query.

		String ex0 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n" + "SELECT ?USER "
				+ "WHERE { ?USER sn:age ?AGE . { ?USER sn:age ?AGE }  UNION  {?USER sn:age ?AGE } }\n";

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

		// MIRAR
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

		String ex36 = "# ?USER : sn:Influencer" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL \r\n" + "}";

		// Second Method. Inconsistent Variable Typing. Ontology Inconsistency.

		String ex37 = "# ?USER : sn:Message" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?MESSAGE sn:attends_to ?USER\r\n" + "}";

		String ex38 = "# ?USER : sn:User" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE \r\n" + "WHERE \r\n" + "{\r\n" + "?MESSAGE sn:attends_to ?USER\r\n" + "}";

		// Second Method. Inconsistent Variable Typing. Constraint Inconsistency.

		String ex39 = "# ?USER : sn:Influencer" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL .\r\n" + "FILTER (?DL < 200) \r\n" + "}";

		String ex40 = "# ?USER : sn:Active" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DA \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyActivity ?DA .\r\n" + "FILTER (?DA < 200) \r\n" + "}";

		// Second Method. Counterexamples of Variable Typing.

		String ex41 = "# ?USER : sn:Influencer" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?DL \r\n" + "WHERE \r\n" + "{\r\n" + "?USER rdf:type sn:User .\r\n"
				+ "?USER sn:dailyLikes ?DL .\r\n" + "FILTER (?DL > 200) \r\n" + "}";

		OWLOntologyManager manager;
		OWLOntologyManager manager_rdf;
		OWLOntologyManager manager_owl;
		OWLOntology ontology;
		OWLOntology ont_rdf;
		OWLOntology ont_owl;
		OWLDataFactory dataFactory;
		OWLDataFactory df_rdf;
		OWLDataFactory df_owl;
		String file = "C:/social-network-2019.owl";
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
				df_owl, "C:/social-network-2019.owl");

		// t.SPARQL_CORRECTNESS(ex31);

		try {
			t.SPARQL_TYPE_VALIDITY(ex41, "DL", "http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#User");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		long estimatedTime = System.currentTimeMillis() - startTime;
		System.out.println("");
		System.out.println("Analysis done in " + estimatedTime + " ms");

	};

}
