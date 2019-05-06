package testingSPARQL;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
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

import org.jpl7.Term;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
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

public class TSPARQL {


	// FILTER && || PENDING
	// SUBPROPERTY - PENDING

	//SELECCIONAR EJEMPLOS - VAADIN

	Integer next = 1;
	Integer current = 0;
	Integer nvar = 0;
	Boolean error = false;
	Boolean negation = false;
	
	List<String> vars = new ArrayList<String>();
	List<List<String>> rules = new ArrayList<List<String>>();
	Map<String, Set<String>> domains_var = new HashMap<String, Set<String>>();
	Map<String, Set<String>> ranges_var = new HashMap<String, Set<String>>();
	Map<String, Set<String>> domains_predicate = new HashMap<String, Set<String>>();
	Map<String, Set<String>> ranges_predicate = new HashMap<String, Set<String>>();
	Set<String> vars_resources = new HashSet<String>();
	Set<String> vars_literals = new HashSet<String>();
	Set<TriplePath> ctriples = new HashSet<TriplePath>();
	Map<String, Map<Node, Set<String>>> ctriplesn = new HashMap<String, Map<Node, Set<String>>>();
	Map<String, String> types_literals = new HashMap<String, String>();
	Set<String> constraints_elements = new HashSet<String>();
	Set<TriplePath> datatriples = new HashSet<TriplePath>();
	OWLOntologyManager manager;
	OWLOntologyManager manager_rdf;
	OWLOntologyManager manager_owl;
	OWLOntology ontology;
	OWLOntology ont_rdf;
	OWLOntology ont_owl;
	OWLDataFactory dataFactory;
	OWLDataFactory df_rdf;
	OWLDataFactory df_owl;
	Boolean missing;
	String file;

	public TSPARQL(OWLOntologyManager manager, OWLOntologyManager manager_rdf, OWLOntologyManager manager_owl,
			OWLOntology ontology, OWLOntology ont_rdf, OWLOntology ont_owl, OWLDataFactory dataFactory,
			OWLDataFactory df_rdf, OWLDataFactory df_owl, String file) {
		this.constraints_elements.clear();
		this.manager = manager;
		this.manager_rdf = manager_rdf;
		this.manager_owl = manager_owl;
		this.ontology = ontology;
		this.ont_rdf = ont_rdf;
		this.ont_owl = ont_owl;
		this.dataFactory = dataFactory;
		this.df_rdf = df_rdf;
		this.df_owl = df_owl;
		this.missing = false;
		this.file = file;

	}

	public String typing() {
		String result = "";
		File fileName = new File(file);
		manager.removeOntology(ontology);
		try {
			ontology = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {

			e2.printStackTrace();
		}
		PelletReasonerFactory f = new PelletReasonerFactory();
		OWLReasoner reasoner = f.createReasoner(ontology);
		if (reasoner.isConsistent()) {
			result = "true";
			reasoner.dispose();
		} else {
			GlassBoxExplanation.setup();
			SingleExplanationGenerator eg = new GlassBoxExplanation(ontology, f);
			try {
				for (OWLAxiom ax : eg.getExplanation(dataFactory.getOWLThing())) {
					result = result + ax.toString() + System.lineSeparator();
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

			e2.printStackTrace();
		}
		PelletReasonerFactory f = new PelletReasonerFactory();
		OWLReasoner reasoner = f.createReasoner(ontology);
		GlassBoxExplanation.setup();
		SingleExplanationGenerator eg = new GlassBoxExplanation(ontology, f);
		try {
			for (OWLAxiom ax : eg.getExplanation(dataFactory.getOWLThing())) {
				result = result + ax.toString() + System.lineSeparator();
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
			e2.printStackTrace();
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
			e2.printStackTrace();
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
			System.out.println("Inconsistent query, please check consistency");
			missing = true;
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

	 
	

	public Set<OWLClassExpression> ClassOfVariable(OWLOntology ont, OWLDataFactory df, IRI iri) {
		File fileName = new File(file);
		manager.removeOntology(ont);
		try {
			ont = manager.loadOntologyFromOntologyDocument(fileName);
		} catch (OWLOntologyCreationException e2) {

			e2.printStackTrace();
		}
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

	public Boolean Existence(TriplePath tp) {
		Boolean result = true;
		if (tp.getSubject().isURI() && !isDeclared(tp.getSubject().getNameSpace(), tp.getSubject().getLocalName())) {
			System.out.println("There is some item not declared in the ontology");
			System.out.println(tp.getSubject());
			result = false;
			missing = true;
		}
		if (tp.getPredicate().isURI()
				&& !isDeclared(tp.getPredicate().getNameSpace(), tp.getPredicate().getLocalName())) {
			System.out.println("There is some item not declared in the ontology");
			System.out.println(tp.getPredicate());
			result = false;
			missing = true;
		}
		if (tp.getObject().isURI() && !isDeclared(tp.getObject().getNameSpace(), tp.getObject().getLocalName())) {
			System.out.println("There is some item not declared in the ontology");
			System.out.println(tp.getObject());
			result = false;
			missing = true;
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
						missing = true;
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
						} else {
							System.out.println("Literal used with an object property or individual");
							missing = true;
						}
					} else /* VUL */
					{
						if (ctriplesn.containsKey(tp.getSubject().getName())) {
							if (ctriplesn.get(tp.getSubject().getName()).containsKey(tp.getPredicate())) {
								ctriplesn.get(tp.getSubject().getName()).get(tp.getPredicate())
										.add(tp.getObject().getLiteral().getValue().toString());
							} else {
								Set<String> content = new HashSet<String>();
								content.add(tp.getObject().getLiteral().getValue().toString());
								ctriplesn.get(tp.getSubject().getName()).put(tp.getPredicate(), content);
							}
						} else {
							Set<String> content = new HashSet<String>();
							content.add(tp.getObject().getLiteral().getValue().toString());
							Map<Node, Set<String>> map = new HashMap<Node, Set<String>>();
							map.put(tp.getPredicate(), content);
							ctriplesn.put(tp.getSubject().getName(), map);
						}					
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
						} else {
							System.out.println("Literal used with an object property or individual");
							missing = true;
						}
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
							e.printStackTrace();
						}
					} else /* LVL */ {
						{
							System.out.println("Literal cannot be used as subject");
							missing = true;
						}
					}
				} else /*-LL*/
				{
					System.out.println("Literal cannot be used as property");
					missing = true;
				}
			}
			else if (tp.getObject().isURI()) {
				if (tp.getSubject().isLiteral()) /* L-U */ {
					System.out.println("Literal cannot be used as subject");
					missing = true;
				} else {
					if (tp.getSubject().isVariable()) {
						if (tp.getPredicate().isLiteral()) /* VLU */ {
							System.out.println("Literal cannot be used as property");
							missing = true;
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
									e.printStackTrace();
								}
							} else {
								System.out.println("Individual used with a data property or individual");
								missing = true;
							}
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
									e.printStackTrace();
								}
							} else /* LVU */ {
								System.out.println("Literal cannot be used as subject");
								missing = true;
							}
						}
					} else {
						if (tp.getPredicate().isLiteral()) /* ULU */
						{
							System.out.println("Literal cannot be a property");
							missing = true;
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
									e.printStackTrace();
								}
							} else {
								System.out.println("Individual used with a data property or individual");
								missing = true;
							}
						}
					}
				}
			}

			else
			if (tp.getSubject().isLiteral()) /* L-V */ {
				System.out.println("Literal cannot be used as subject");
				missing = true;
			} else if (tp.getSubject().isVariable()) {
				if (tp.getPredicate().isLiteral()) /* VLV */
				{
					System.out.println("Literal cannot be a predicate");
					missing = true;
				} else if (tp.getPredicate().isURI()) /* VUV */
				{
					ctriples.add(tp);
					if (ctriplesn.containsKey(tp.getSubject().getName())) {
						if (ctriplesn.get(tp.getSubject().getName()).containsKey(tp.getPredicate())) {
							ctriplesn.get(tp.getSubject().getName()).get(tp.getPredicate())
									.add(tp.getObject().getName());
						} else {
							Set<String> content = new HashSet<String>();
							content.add(tp.getObject().getName());
							ctriplesn.get(tp.getSubject().getName()).put(tp.getPredicate(), content);
						}
					} else {
						Set<String> content = new HashSet<String>();
						content.add(tp.getObject().getName());
						Map<Node, Set<String>> map = new HashMap<Node, Set<String>>();
						map.put(tp.getPredicate(), content);
						ctriplesn.put(tp.getSubject().getName(), map);
					}

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
						OWLNamedIndividual ni1 = null;
						ni1 = dft.getOWLNamedIndividual(IRI.create(urio + '#' + tp.getObject().getName().substring(0)));
						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
						mng.applyChange(addAxiom1);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							e.printStackTrace();
						}
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
								e.printStackTrace();
							}
							addTypeVariable(tp.getObject().getName().substring(0).toUpperCase(),
									"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
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
							 
							e.printStackTrace();
						}
					}
					else {
						missing = true;
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
						e.printStackTrace();
					}
				}
			} else {
				if (tp.getPredicate().isLiteral()) /* ULV */ {
					System.out.println("Literal cannot be a predicate");
					missing = true;
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
						OWLClass cls = dft.getOWLClass(IRI.create("http://www.w3.org/2000/01/rdf-schema#Literal"));
						OWLAxiom axiom1 = dft.getOWLClassAssertionAxiom(cls, ni1);
						AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);
						mng.applyChange(addAxiom1);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {						 
							e.printStackTrace();
						}
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
								e.printStackTrace();
							}
							addTypeVariable(tp.getObject().getName().substring(0).toUpperCase(),
									"http://www.types.org#" + t.substring(t.lastIndexOf('#') + 1));
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
						// RDF:TYPE IS TREATED AS OBJECT PROPERTY
						OWLAxiom axiom2 = dft.getOWLObjectPropertyAssertionAxiom(o, ni1, ni2);
						AddAxiom addAxiom2 = new AddAxiom(ont, axiom2);
						mng.applyChange(addAxiom2);
						try {
							mng.saveOntology(ont);
						} catch (OWLOntologyStorageException e) {
							e.printStackTrace();
						}
					} else {
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
						e.printStackTrace();
					}
				}
			}
		} else {}
	};

	public List<List<String>> SPARQL_ANALYSIS(String file, String queryString, Integer step) {
		
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

        OWLDisjointClassesAxiom ax1 = dataFactory.getOWLDisjointClassesAxiom(dt,st);
        OWLDisjointClassesAxiom ax2 =dataFactory.getOWLDisjointClassesAxiom(dt,intt);
        OWLDisjointClassesAxiom ax3 =dataFactory.getOWLDisjointClassesAxiom(dt,pintt);
        OWLDisjointClassesAxiom ax4 =dataFactory.getOWLDisjointClassesAxiom(dt,nintt);
        OWLDisjointClassesAxiom ax5 =dataFactory.getOWLDisjointClassesAxiom(dt,npintt);
        OWLDisjointClassesAxiom ax6 =dataFactory.getOWLDisjointClassesAxiom(dt,nnintt);
        OWLDisjointClassesAxiom ax7 =dataFactory.getOWLDisjointClassesAxiom(dt,dou);
        OWLDisjointClassesAxiom ax8 =dataFactory.getOWLDisjointClassesAxiom(dt,flo);
        OWLDisjointClassesAxiom ax9 =dataFactory.getOWLDisjointClassesAxiom(dt,dec);


       
        OWLDisjointClassesAxiom ax10 =dataFactory.getOWLDisjointClassesAxiom(st,intt);
        OWLDisjointClassesAxiom ax11 =dataFactory.getOWLDisjointClassesAxiom(st,pintt);
        OWLDisjointClassesAxiom ax12 =dataFactory.getOWLDisjointClassesAxiom(st,nintt);
        OWLDisjointClassesAxiom ax13 =dataFactory.getOWLDisjointClassesAxiom(st,npintt);
        OWLDisjointClassesAxiom ax14 =dataFactory.getOWLDisjointClassesAxiom(st,nnintt);
        OWLDisjointClassesAxiom ax15 =dataFactory.getOWLDisjointClassesAxiom(st,dou);
        OWLDisjointClassesAxiom ax16 =dataFactory.getOWLDisjointClassesAxiom(st,flo);
        OWLDisjointClassesAxiom ax17 =dataFactory.getOWLDisjointClassesAxiom(st,dec);

        OWLDisjointClassesAxiom ax18 =dataFactory.getOWLDisjointClassesAxiom(nintt,pintt);

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
			e.printStackTrace();
		}

		
		final Query query = QueryFactory.create(queryString);
		if (	query.isConstructType() ||
				query.isAskType() ||
				query.isDescribeType() ||
				query.isDistinct() ||
				query.hasAggregators() ||
				query.hasOrderBy() ||
				query.hasGroupBy() ||
				query.hasHaving() ||
				query.hasOffset() ||
				!query.getGraphURIs().isEmpty() ||
				!query.getNamedGraphURIs().isEmpty() ||
				query.hasLimit() )
		{
			System.out.println("SPARQL expression not supported");
			missing = true;
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
			String urio = ontology.getOntologyID().getOntologyIRI().toString();
			for (TriplePath tp : ctriples) {
				Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
				datatriples.add(tp);
				if (!(typ == null)) {
					for (OWLClassExpression c : typ) {
						OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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
				missing = true;
				rules.clear();
			}
			String urio = ontology.getOntologyID().getOntologyIRI().toString();
			for (TriplePath tp : ctriples) {
				Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
				datatriples.add(tp);
				if (!(typ == null)) {
					for (OWLClassExpression c : typ) {
						OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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
			negation = true;
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
				missing = true;
				rules.clear();
			}
			String head;
			String urio = ontology.getOntologyID().getOntologyIRI().toString();
			for (TriplePath tp : ctriples) {
				Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
				datatriples.add(tp);
				if (!(typ == null)) {
					for (OWLClassExpression c : typ) {
						OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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
			constraints_elements.add(el.getExpr().toString());
			List<String> ss = new ArrayList<>(SExprtoPTerm(el.getExpr(), null));
			for (int i = 0; i < ss.size(); i++) {
				rules.get(current).add(ss.get(i));
			}
		} else {missing = true; System.out.println("Expression "+el.getExpr().getFunction().getFunctionName(null)+ " not allowed in FILTER expression");}
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
				missing = true;
				rules.clear();
			}
			String urio = ontology.getOntologyID().getOntologyIRI().toString();
			for (TriplePath tp : ctriples) {
				Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
						IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
				datatriples.add(tp);
				if (!(typ == null)) {
					for (OWLClassExpression c : typ) {
						OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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
				missing = true;
				rules.clear();
			}
		}
	}

	public void elementMinus(ElementMinus el, Integer step, String fileo) {
		negation = true;
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
			missing = true;
			rules.clear();
		}

		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		for (TriplePath tp : ctriples) {
			Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
			datatriples.add(tp);
			if (!(typ == null)) {
				for (OWLClassExpression c : typ) {
					OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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
		negation = true;
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
			missing = true;
			rules.clear();
		}
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		for (TriplePath tp : ctriples) {
			Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
			datatriples.add(tp);
			if (!(typ == null)) {
				for (OWLClassExpression c : typ) {
					OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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
		if ( 
				query.isConstructType() ||
				query.isAskType() ||
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
			missing = true;
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
			missing = true;
			rules.clear();
		}
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		for (TriplePath tp : ctriples) {
			Set<OWLClassExpression> typ = ClassOfVariable(ontology, dataFactory,
					IRI.create(urio + '#' + tp.getSubject().getName().substring(0)));
			datatriples.add(tp);
			if (!(typ == null)) {
				for (OWLClassExpression c : typ) {
					OWLRestriction(c.asOWLClass(), tp.getSubject().getName(), step);
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

	public void OWLRestriction(OWLClass ce, String var_name, Integer step) {
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
				Set<OWLClassExpression> ec = arg0.getOperands();
				for (OWLClassExpression e : ec) {
					e.accept(this);
					rules.get(current).add(";");
				}
				rules.get(current).add("true");
			}
			@Override
			public void visit(OWLObjectComplementOf arg0) {
				// PELLET
			}
			@Override
			public void visit(OWLObjectSomeValuesFrom arg0) {
			}
			@Override
			public void visit(OWLObjectAllValuesFrom arg0) {
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
						Map<Node, Set<String>> uses = ctriplesn.get(var_name);
						if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
							Set<String> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
							String cons = "";						
							for (String var : vars_) {
								OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;
								if (r.getDatatype().isInteger()) {
									for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
										if (fr.getFacet().toString() == "maxExclusive") {
											cons = cons + 
												var.toUpperCase() + "#<" + fr.getFacetValue().getLiteral()
												+ ",";
											constraints_elements.add("("+var.toUpperCase() + "<" 
												+ fr.getFacetValue().getLiteral()+")");
										} else if (fr.getFacet().toString() == "maxInclusive") {
											cons = cons + 
												var.toUpperCase() + "#<=" + fr.getFacetValue().getLiteral()
												+ ",";
											constraints_elements.add("("+var.toUpperCase() + "<=" 
												+ fr.getFacetValue().getLiteral()+")");
										} else if (fr.getFacet().toString() == "minExclusive") {
											cons = cons + 
												var.toUpperCase() + "#>" + fr.getFacetValue().getLiteral()
												+ ",";
											constraints_elements.add("("+var.toUpperCase() + ">" 
												+ fr.getFacetValue().getLiteral()+")");
										} else if (fr.getFacet().toString() == "minInclusive") {
											cons = cons + 
												var.toUpperCase() + "#>=" + fr.getFacetValue().getLiteral()
												+ ",";
											constraints_elements.add("("+var.toUpperCase() + ">=" + 
												fr.getFacetValue().getLiteral()+")");
										}
									}
								} else 
									if (r.getDatatype().isFloat() || 
											r.getDatatype().isDouble() 
										) {
										for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
											if (fr.getFacet().toString() == "maxExclusive") {
												cons = cons + 
												"{" + var.toUpperCase() + "<" + fr.getFacetValue().getLiteral().toString() +"}"
												+ ",";
												constraints_elements.add("("+var.toUpperCase() + "<" 
												+ fr.getFacetValue().getLiteral()+")");
											} else if (fr.getFacet().toString() == "maxInclusive") {
												cons = cons 
												+ "{"+ var.toUpperCase() + "<=" + fr.getFacetValue().getLiteral().toString() + "}"
												+ ",";
												constraints_elements.add("("+var.toUpperCase() + "<=" 
												+ fr.getFacetValue().getLiteral()+")");
											} else if (fr.getFacet().toString() == "minExclusive") {
												cons = cons 
												+ "{"+ var.toUpperCase() + ">" + fr.getFacetValue().getLiteral().toString() + "}"
												+ ",";
												constraints_elements.add("("+var.toUpperCase() + ">" 
												+ fr.getFacetValue().getLiteral()+")");
											} else if (fr.getFacet().toString() == "minInclusive") {
												cons = cons 
												+ "{"+ var.toUpperCase() + ">=" + fr.getFacetValue().getLiteral().toString() +"}"
												+ ",";
												constraints_elements.add("("+var.toUpperCase() + ">=" 
												+ fr.getFacetValue().getLiteral()+")");
											}
										}
									} else {missing=true;System.out.println("OWL Restriction not allowed");}
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
						addTypeVariable("B" + act, types_literals.get("A" + act));
					} else
					if (types_literals.containsKey("B" + act)) {
						types_literals.put("A" + act,
								types_literals.get("B" + act));
						addTypeVariable("A" + act, types_literals.get("B" + act));
					}
					else {
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
					if (types_literals.containsKey("B" + act))
					{
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
						else {
							System.out.println("Error: Some variable is not typed");
							missing = true;
						}
					} else {
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
					nvar++;
				} else {
				}
			}
		} else
		if (st.isVariable()) {
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
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
				} else {
					System.out.println("Error: Some variable is not typed");
					missing = true;
				}
			} else {
				System.out.println("Error: Some variable is not typed");
				missing = true;
			}

		} else if (st.isConstant()) {

			if (isValidFormat("dd/MM/yyyy", st.toString(), Locale.ENGLISH)) {
				addTypeVariable(var.toString().replace('?', ' ').replaceAll("\\s", "").toUpperCase(),
						"http://www.types.org#xsd:dateTime");
				DateTimeFormatter fomatter = DateTimeFormatter.ofPattern("dd/MM/yyyy", Locale.ENGLISH);
				LocalDateTime ldt = LocalDateTime.parse(st.toString(), fomatter);
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
				if (types_literals.containsKey("A" + act))
				{
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
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
				} else {
					System.out.println("Error: Some variable is not typed");
					missing = true;
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
					}
					else if (types_literals.get("B" + act).equals("http://www.types.org#xsd:double")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:float")
							|| types_literals.get("B" + act).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + "B" + act + " =:= " + "V" + act + " }");
					} else {
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
				} else {
					System.out.println("Error: Some variable is not typed");
					missing = true;
				}
				types_literals.put("W" + act, types_literals.get("U" + act));
				if (types_literals.containsKey("W" + act)) {
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
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
				} else {
					System.out.println("Error: Some variable is not typed");
					missing = true;
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
					}
					else if (types_literals.get(res).equals("http://www.types.org#xsd:float")
							|| types_literals.get(res).equals("http://www.types.org#xsd:double")
							|| types_literals.get(res).equals("http://www.types.org#xsd:decimal")) {
						pt.add("{" + res + " =:=" + "W" + act + " }");
					} else {
						System.out.println("Error: Some variable is not typed");
						missing = true;
					}
				} else {
					System.out.println("Error: Some variable is not typed");
					missing = true;
				}
				nvar++;
			} else {}
		}
		return pt;
	}

	public void addTypeVariable(String variable, String type) {
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		OWLNamedIndividual ni = dataFactory.getOWLNamedIndividual(IRI.create(urio + '#' + variable));
		if (type == null) {
			missing = true;
			System.out.println("Error: Some variable is not typed");
		} else {
			OWLClass cls = dataFactory.getOWLClass(IRI.create(type));
			OWLAxiom axiom1 = dataFactory.getOWLClassAssertionAxiom(cls, ni);
			AddAxiom addAxiom1 = new AddAxiom(ontology, axiom1);
			manager.applyChange(addAxiom1);
			try {
				manager.saveOntology(ontology);
			} catch (OWLOntologyStorageException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
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
			e.printStackTrace();
		}

	}

	public void removeTypeAssertion(OWLClassExpression cls, OWLNamedIndividual ni) {
		OWLAxiom axiom1 = dataFactory.getOWLClassAssertionAxiom(cls, ni);
		RemoveAxiom addAxiom1 = new RemoveAxiom(ontology, axiom1);
		manager.applyChange(addAxiom1);
		try {
			manager.saveOntology(ontology);
		} catch (OWLOntologyStorageException e) {
			e.printStackTrace();
		}

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

	public void SPARQL_CONSTRAINTS_CHECKING(List<List<String>> rules) {

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
			if (!missing) {
				System.out.println("Unsuccessful Checking due to:");
				for (String c : constraints_elements) {
					System.out.print(c + " ");
				}
			}
		} else {
			if (!missing)
				System.out.println("Successful Checking");
		}
	}

	public void SPARQL_TYPING(String query) {

		copy(file);
		next = 1;
		current = 0;
		nvar = 0;
		vars.clear();
		rules.clear();
		SPARQL_ANALYSIS(file, query, 0);
		
		if (negation) {System.out.println("The query contains negative constraints: OPTIONAL, MINUS or NOT EXISTS. "
				+ "They are not allowed in Type Checking.");}
		else {
		String r = "";
		if (!missing) {
			r = typing();
		}	
		if (!(r == "true")) {
			if (!missing) {
				System.out.println("Unsuccessful Typing due to:");
				System.out.print(r);
			}
		} else {
			if (!missing)
				System.out.println("Successful Typing");
		}
		}
		restore(file);
	}

	public void SPARQL_CHECKING(String query) {
		copy(file);
		next = 1;
		current = 0;
		nvar = 0;
		vars.clear();
		rules.clear();
		SPARQL_ANALYSIS(file, query, 0);
		restore(file);
		SPARQL_CONSTRAINTS_CHECKING(rules);
	}

	public void SPARQL_TESTING(String query, String var_name, String type_name) {

		copy(file);
		next = 1;
		current = 0;
		nvar = 0;
		vars.clear();
		rules.clear();
		SPARQL_ANALYSIS(file, query, 0);
		if (negation) {System.out.println("The query contains negative constraints: OPTIONAL, MINUS or NOT EXISTS. "
				+ "They are not allowed in Testing.");}
		else {
		String urio = ontology.getOntologyID().getOntologyIRI().toString();
		OWLClass ce = dataFactory.getOWLClass(IRI.create(type_name));
		OWLNamedIndividual in = dataFactory.getOWLNamedIndividual(IRI.create(urio + '#' + var_name));
		OWLTesting(ce, in, var_name);
		if (!error && !missing) {
			System.out.println("Successful testing. The property has been proved");
		}	
		}
		restore(file);
	}

	public void OWLTesting(OWLClass ce, OWLNamedIndividual in, String var_name) {		
		OWLClassExpressionVisitor cv = new OWLClassExpressionVisitor() {
			Boolean union = false;
			@Override
			public void visit(OWLClass arg0) {
				OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
				String entailment = entailment(axiom);
				if (entailment == "true") {
				} else {
					addTypeAssertion(arg0, in);
					String consistency = consistency();
					if (consistency == "true") {
					} else {
						error = true;
						if (!union) {
							System.out
									.println("Unsuccessful Testing. Case 1.1. Caused by the following inconsistency:");
							System.out.print(explanations());
							System.out.println(arg0);
						}
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
				Boolean each = false;
				union = true;
				Set<OWLClassExpression> ec = arg0.getOperands();
				for (OWLClassExpression e : ec) {
					e.accept(this);
					each = !error || each;
				}
				if (!each) {
					System.out
							.println("Unsuccessful Testing. Case 2. The following class membership cannot be proved:");
					System.out.println(in);
					System.out.println("rdf:type");
					System.out.println(arg0);
				}
				union = false;
			}

			@Override
			public void visit(OWLObjectComplementOf arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 3. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 3.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectSomeValuesFrom arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 4. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 4.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectAllValuesFrom arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 5. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 5.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectHasValue arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 6. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 6.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectMinCardinality arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 7. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 7.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}

			}

			@Override
			public void visit(OWLObjectExactCardinality arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 8. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 8.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectMaxCardinality arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 9. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 9.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLObjectHasSelf arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 10. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 10.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
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
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 11. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 11.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}

			}

			@Override
			public void visit(OWLDataAllValuesFrom arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 12. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 12.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
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
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 13. The following class membership cannot be proved:");
								System.out.println(in);
								System.out.println("rdf:type");
								System.out.println(arg0);
							}
						} else {
							addTypeAssertion(arg0, in);
							String consistency = consistency();
							if (consistency == "true") {
							} else {
								error = true;
								if (!union) {
									System.out.println(
											"Unsuccessful Testing. Case 13.1. Caused by the following inconsistency:");
									System.out.print(explanations());
									System.out.println(arg0);
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
								Map<Node, Set<String>> uses = ctriplesn.get(var_name);
								if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
									Set<String> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
									String cons = "";
									for (String var : vars_) {
										OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;
										if (r.getDatatype().isInteger()) {
											for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
												if (fr.getFacet().toString() == "maxExclusive") {
													cons = cons + "#\\" + var.toUpperCase() + "#<"
															+ fr.getFacetValue().getLiteral() + ",";
													constraints_elements.add("("+var.toUpperCase() + "<"
															+ fr.getFacetValue().getLiteral()+")");
												} else if (fr.getFacet().toString() == "maxInclusive") {
													cons = cons + "#\\" + var.toUpperCase() + "#<="
															+ fr.getFacetValue().getLiteral() + ",";
													constraints_elements.add("("+var.toUpperCase() + "<="
															+ fr.getFacetValue().getLiteral()+")");
												} else if (fr.getFacet().toString() == "minExclusive") {
													cons = cons + "#\\" + var.toUpperCase() + "#>"
															+ fr.getFacetValue().getLiteral() + ",";
													constraints_elements.add("("+var.toUpperCase() + ">"
															+ fr.getFacetValue().getLiteral()+")");
												} else if (fr.getFacet().toString() == "minInclusive") {
													cons = cons + "#\\" + var.toUpperCase() + "#>="
															+ fr.getFacetValue().getLiteral() + ",";
													constraints_elements.add("("+var.toUpperCase() + ">="
															+ fr.getFacetValue().getLiteral()+")");
												}
											}
										}
										else if (r.getDatatype().isDouble()
												|| r.getDatatype().isFloat()) {
											for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
												if (fr.getFacet().toString() == "maxExclusive") {
													cons = cons  + "{"+ var.toUpperCase() + ">="
															+ fr.getFacetValue().getLiteral().toString() +"}" + ",";
													constraints_elements.add("("+var.toUpperCase() + "<"
															+ fr.getFacetValue().getLiteral()+")");
												} else if (fr.getFacet().toString() == "maxInclusive") {
													cons = cons  + "{"+ var.toUpperCase() + ">"
															+ fr.getFacetValue().getLiteral().toString()+ "}" + ",";
													constraints_elements.add("("+var.toUpperCase() + "<="
															+ fr.getFacetValue().getLiteral()+")");
												} else if (fr.getFacet().toString() == "minExclusive") {
													cons = cons  + "{"+  var.toUpperCase() + "=<"
															+ fr.getFacetValue().getLiteral().toString() +"}" + ",";
													constraints_elements.add("("+var.toUpperCase() + ">"
															+ fr.getFacetValue().getLiteral()+")");
												} else if (fr.getFacet().toString() == "minInclusive") {
													cons = cons + "{" + var.toUpperCase() + "<"
															+ fr.getFacetValue().getLiteral().toString() + "}" + ",";
													constraints_elements.add("("+var.toUpperCase() + ">="
															+ fr.getFacetValue().getLiteral()+")");
												}
											}
										} else {error=true;System.out.println("OWL Restriction not allowed");}										
									}
									String domain = "";
									Map<String, String> rename = new HashMap<String, String>();
									for (String v : vars_) {
										if (types_literals.containsKey(v)) {
											if (types_literals.get(v).equals("http://www.types.org#xsd:integer")
													|| types_literals.get(v).equals("http://www.types.org#xsd:string")
													|| types_literals.get(v).equals("http://www.types.org#xsd:dateTime")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:positiveInteger")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:negativeInteger")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:nonPositiveInteger")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:nonNegativeInteger"))
											{
												Integer act = nvar;
												nvar++;
												domain = domain + "fd_dom(" + v + ",R" + act + ")" + ",";
												rename.put("R" + act, v);
											} else {
												if (types_literals.get(v).equals("http://www.types.org#xsd:float")
														|| types_literals.get(v)
																.equals("http://www.types.org#xsd:double")
														|| types_literals.get(v)
																.equals("http://www.types.org#xsd:decimal")) {
													Integer act = nvar;
													nvar++;
													domain = domain + "(sup(" + v + ",S),inf(" + v + ",I)->R" + act
															+ "=..['..',I,S];" + "(sup(" + v + ",S)->R" + act
															+ "=..['..',inf,S];" + "inf(" + v + ",I)->R" + act
															+ "=..['..',I,sup];" + "R" + act + "=..['..',inf,sup]))"
															+ ",";
													rename.put("R" + act, v);
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
										String head = newhead + "," + cons + "," + domain;
										org.jpl7.Query qimpl = new org.jpl7.Query(head);
										if (qimpl.hasSolution())
										{
											error = true;
											if (!union) {
												System.out.println("Unsuccessful Testing. Case 14. Counterexample:");
												Map<String, Term>[] sols = qimpl.allSolutions();
												for (Map<String, Term> s : sols) {
													for (String key : s.keySet())
														if (s.get(key).isCompound()) {
															System.out.println(rename.get(key) + "=" + s.get(key));
														}
												}
											}
										} else {
											cons = "";
											for (String var : vars_) {
												OWLDatatypeRestriction r = (OWLDatatypeRestriction) filler;
												if (r.getDatatype().isInteger()) {
													for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
														if (fr.getFacet().toString() == "maxExclusive") {
															cons = cons + var.toUpperCase() + "#<"
																	+ fr.getFacetValue().getLiteral() + ";";
														} else if (fr.getFacet().toString() == "maxInclusive") {
															cons = cons + var.toUpperCase() + "#<="
																	+ fr.getFacetValue().getLiteral() + ";";
														} else if (fr.getFacet().toString() == "minExclusive") {
															cons = cons + var.toUpperCase() + "#>"
																	+ fr.getFacetValue().getLiteral() + ";";
														} else if (fr.getFacet().toString() == "minInclusive") {
															cons = cons + var.toUpperCase() + "#>="
																	+ fr.getFacetValue().getLiteral() + ";";
														}
													}
												} else
													if (r.getDatatype().isFloat()||
															r.getDatatype().isDouble()) {
														for (OWLFacetRestriction fr : r.getFacetRestrictions()) {
															if (fr.getFacet().toString() == "maxExclusive") {
																cons = cons + "{"+ var.toUpperCase() + "<"
																		+ fr.getFacetValue().getLiteral() + "}" + ";";
															} else if (fr.getFacet().toString() == "maxInclusive") {
																cons = cons + "{" + var.toUpperCase() + "<="
																		+ fr.getFacetValue().getLiteral() +"}" + ";";
															} else if (fr.getFacet().toString() == "minExclusive") {
																cons = cons + "{"+ var.toUpperCase() + ">"
																		+ fr.getFacetValue().getLiteral() +"}" + ";";
															} else if (fr.getFacet().toString() == "minInclusive") {
																cons = cons + "{" + var.toUpperCase() + ">="
																		+ fr.getFacetValue().getLiteral() +"}" + ";";
															}
														}
													} else {error=true;System.out.println("OWL Restriction not allowed");}
											}
											if (!cons.isEmpty()) {
												cons = cons.substring(0, cons.length() - 1);
											}
											newhead = "";
											for (int i = 1; i < rules.get(0).size(); i++) {
												newhead = newhead + rules.get(0).get(i) + ',';
											}
											if (!newhead.isEmpty())
											{
												newhead = newhead.substring(0, newhead.length() - 1);
												head = newhead + "," + cons;
												org.jpl7.Query qcons = new org.jpl7.Query(head);
												if (!qcons.hasSolution()) {
													error = true;
													if (!union) {
														System.out.println(
																"Unsuccessful Testing. Case 14.1. Caused by the following inconsistency");
														System.out.println(head);
													}
												} else {
													head = newhead + "->" + cons;
													qcons = new org.jpl7.Query(head);
													if (qcons.hasSolution()) {
													} else {}
												}
											}
											else {
												error = true;
												if (!union) {
													System.out.println(
															"Unsuccessful Testing. Case 14.2. The following expression cannot be proved");
													System.out.println(head);
												}
											}
										}
									}
									else {
										error = true;
										if (!union) {
											System.out.println(
													"Unsuccessful Testing. Case 14.3. The following expression cannot be proved");
											for (String c : constraints_elements) {
												System.out.print(c);
											}
										}
									}
								} else {
									error = true;
									if (!union) {
										System.out.println(
												"Unsuccessful Testing. Case 14.4. The property cannot be proved. "
														+ "Not enough information for:");
										System.out.println(dp.getIRI().toString());
									}
								}
							}
						} else {
							error = true;
							if (!union) {
								System.out.println("Unsuccessful Testing. Case 14.5 . The property cannot be proved. "
										+ "Not enough information for:");
								System.out.println(var_name);
							}
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
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 17. The following class membership cannot be proved:");
								System.out.println(in);
								System.out.println("rdf:type");
								System.out.println(arg0);
							}
						} else {
							addTypeAssertion(arg0, in);
							String consistency = consistency();
							if (consistency == "true") {
							} else {
								error = true;
								if (!union) {
									System.out.println(
											"Unsuccessful Testing. Case 17.1. Caused by the following inconsistency:");
									System.out.print(explanations());
									System.out.println(arg0);
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
								Map<Node, Set<String>> uses = ctriplesn.get(var_name);
								if (uses.containsKey(Node.createURI(dp.getIRI().toString()))) {
									String cons = "";
									Set<String> vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
									for (String var : vars_) {
										if (val.isInteger()) {
											cons = cons + "#\\" + var.toUpperCase() + "#=" + val.getLiteral();
											constraints_elements.add("("+var.toUpperCase() + "=" + val.getLiteral()+")");
										}
										else if (val.isFloat() || val.isDouble() ) {
											cons = cons + "{" + var.toUpperCase() + "=\\=" + val.getLiteral().toString() +"}" 
											 ;
											constraints_elements.add("("+var.toUpperCase() + "=" + val.getLiteral()+")");
										}
									}
									String domain = "";
									Map<String, String> rename = new HashMap<String, String>();
									for (String v : vars_) {
										if (types_literals.containsKey(v)) {
											if (types_literals.get(v).equals("http://www.types.org#xsd:integer")
													|| types_literals.get(v).equals("http://www.types.org#xsd:string")
													|| types_literals.get(v).equals("http://www.types.org#xsd:dateTime")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:positiveInteger")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:negativeInteger")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:nonPositiveInteger")
													|| types_literals.get(v)
															.equals("http://www.types.org#xsd:nonNegativeInteger"))
											{
												Integer act = nvar;
												nvar++;
												domain = domain + "fd_dom(" + v + ",R" + act + ")" + ",";
												rename.put("R" + act, v);
											} else {
												if (types_literals.get(v).equals("http://www.types.org#xsd:float")
														|| types_literals.get(v)
																.equals("http://www.types.org#xsd:double")
														|| types_literals.get(v)
																.equals("http://www.types.org#xsd:decimal")) {
													Integer act = nvar;
													nvar++;
													domain = domain + "(sup(" + v + ",S),inf(" + v + ",I)->R" + act
															+ "=..['..',I,S];" + "(sup(" + v + ",S)->R" + act
															+ "=..['..',inf,S];" + "inf(" + v + ",I)->R" + act
															+ "=..['..',I,sup];" + "R" + act + "=..['..',inf,sup]))"
															+ ",";
													rename.put("R" + act, v);
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
										String head = newhead + "," + cons + "," + domain;
										org.jpl7.Query qimpl = new org.jpl7.Query(head);
										if (qimpl.hasSolution())
										{
											error = true;
											if (!union) {
												System.out.println("Unsuccessful Testing. Case 18. Counterexample:");
												Map<String, Term>[] sols = qimpl.allSolutions();
												for (Map<String, Term> s : sols) {
													for (String key : s.keySet())
														if (s.get(key).isCompound()) {
															System.out.println(rename.get(key) + "=" + s.get(key));
														}
												}
											}
										}
										else {
											vars_ = uses.get(Node.createURI(dp.getIRI().toString()));
											cons = "";
											for (String var : vars_) {
												if (val.isInteger()) {
													cons = cons + var.toUpperCase() + "#=" + val.getLiteral();
												}
												else if (val.isFloat() || val.isDouble()) {
													cons = cons + "{"+ var.toUpperCase() + "=:=" + val.getLiteral() +"}";
												} else {error=true;System.out.println("OWL Restriction not allowed");}
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
													error = true;
													if (!union) {
														System.out.println(
																"Unsuccessful Testing. Case 18.1. Caused by the following inconsistency");
														System.out.println(head);
													}
												} else {
													head = newhead + "->" + cons;
													qcons = new org.jpl7.Query(head);
													if (qcons.hasSolution()) {
													} else {}
												}
											} else {
												error = true;
												if (!union) {
													System.out.println(
															"Unsuccessful Testing. Case 18.2. The following expression cannot be proved");
													System.out.println(cons);
												}
											}
										}
									} else {
										error = true;
										if (!union) {
											System.out.println(
													"Unsuccessful Testing. Case 18.3. The following expression cannot be proved:");
											for (String c : constraints_elements)
											{System.out.print(c);							
											}
										}
									    }
										}
										else {
											error = true;
											if (!union) {
												System.out.println(
														"Unsuccessful Testing. Case 18.4. The property cannot be proved. "
																+ "Not enough information for: ");
												System.out.println(dp.getIRI().toString());
											}
										}
									}
								}
								else {
									error = true;
									if (!union) {
										System.out.println(
												"Unsuccessful Testing. Case 18.5. The property cannot be proved. "
														+ "Not enough information for: ");
										System.out.println(var_name);
									}
								}
							}
						}
			}

			@Override
			public void visit(OWLDataMinCardinality arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 19. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 19.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLDataExactCardinality arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 20. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 20.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}

			@Override
			public void visit(OWLDataMaxCardinality arg0) {
				if (!error) {
					OWLAxiom axiom = dataFactory.getOWLClassAssertionAxiom(arg0, in);
					String entailment = entailment(axiom);
					if (entailment == "false") {
						error = true;
						if (!union) {
							System.out.println(
									"Unsuccessful Testing. Case 22. The following class membership cannot be proved:");
							System.out.println(in);
							System.out.println("rdf:type");
							System.out.println(arg0);
						}
					} else {
						addTypeAssertion(arg0, in);
						String consistency = consistency();
						if (consistency == "true") {
						} else {
							error = true;
							if (!union) {
								System.out.println(
										"Unsuccessful Testing. Case 22.1. Caused by the following inconsistency:");
								System.out.print(explanations());
								System.out.println(arg0);
							}
						}
						removeTypeAssertion(arg0, in);
					}
				}
			}
		};

		if (!missing) {ce.accept(cv);}
	}

	public void copy(String file) {
		FileInputStream source = null;
		FileOutputStream dest = null;
		try {
			source = new FileInputStream(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		try {
			dest = new FileOutputStream("tmp.owl");
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		byte[] buffer = new byte[1024];
		int length;
		try {
			while ((length = source.read(buffer)) > 0) {
				dest.write(buffer, 0, length);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

	};

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

	public static void main(String[] args) {

		// Wrong type 0
		String type0 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { sn:foo sn:attends_to sn:empty }\n";
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
				+ "SELECT ?USER WHERE { ?USER ?Prop sn:User . ?Prop rdf:type sn:Event  }\n";

		// Wrong type 12 --correcta
		String type12 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER ?Prop sn:User . ?USER rdf:type ?Prop  }\n";

		// Wrong type 13
		String type13 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE { ?USER ?Prop ?Value . ?USER sn:name ?Prop }\n";

		// Wrong type 14  
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
				+ "SELECT ?USER WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE = 50) "
				+ ". BIND ((?AGE+?AGE) AS ?U) . FILTER(?U = 10)}";

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

		String val17 = "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?CARD WHERE {\n" + "?PROP owl:minCardinality ?CARD . \n" + " FILTER(?CARD = -1)}\n";

		String test1 = "# ?USER rdf:type Verified" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER   WHERE {\n ?USER sn:verified ?V . FILTER(?V = 1)" + "}";

		String test2 = "# ?USER rdf:type Verified" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER   WHERE {\n ?USER sn:verified ?V . FILTER(?V > 1)" + "}";

		String test3 = "# ?USER rdf:type Verified" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER   WHERE {\n ?USER sn:verified ?V" + "}";

		String test4 = "# ?USER rdf:type Influencer" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER   WHERE {\n ?USER sn:nfollowers ?NF . ?USER sn:nfollowers ?NF2 . FILTER(?NF <100)"
				+ "}";

		String test5 = "# ?USER rdf:type Influencer" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER   WHERE {\n ?USER sn:nfollowers ?NF . ?USER sn:nfollowers ?NF2 . FILTER(?NF <800) ."
				+ "FILTER(?NF2 <200) "
				+ "}";

		String test6 = "# ?USER rdf:type Influencer" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER   WHERE {\n ?USER rdf:type sn:User . ?USER sn:age ?Y " + "}";

		String test7 = "# ?USER rdf:type Leader" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE ?MESSAGE  WHERE {\n ?USER rdf:type sn:User . " + "{SELECT ?MESSAGE WHERE {\n"
				+ "?MESSAGE sn:sent_by ?USER  }}}\n";

		// Answer: MESSAGE is not of type Shared

		String test8 = "#?USER rdf:type Young" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER1 ?USER2 ?AU1 ?AU2 WHERE {\n" + "?USER1 sn:age ?AU1 . ?USER2 sn:age ?AU2 . \n "
				+ "FILTER(?AU1-?AU2 < 10) .\n" + "FILTER(?AU1 > 20 ).\n" + "FILTER (?AU2 < 18) }\n";

		// Au1 is smaller than 38

		String test9 = "#?USER rdf:type Young" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE WHERE {\n" + "?USER sn:age ?AGE .\n" + "FILTER (?AGE < 50) .\n"
				+ "FILTER EXISTS {SELECT ?USER2 WHERE {\n" + "?USER2 sn:age ?AGE2 .\n" + "FILTER (?AGE2 < 25) .\n"
				+ "FILTER (?AGE < ?AGE2 ) }\n" + "}}\n";

		// Answer: Age is smaller than 25

		String test10 = "# ?USER rdf:type Young" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: Age of User is greater than 40

		String test11 = "# ?MESSAGE rdf:type Shared" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: Message has not been shared by an user

		String test12 = "# ?USER sn:likes ?MESSAGE" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: No

		String test13 = "# ?USER rdf:type sn:Young" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: Age of user is greater than 40

		String test14 = "# ?USER rdf:type sn:Mature" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: Yes

		String test15 = "# ?USER rdf:type sn:Event" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: Event has empty intersection with User

		String test16 = "# ?USER2 sn:likes ?MESSAGE" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER ?MESSAGE ?AGE WHERE {\n" + "?USER sn:age ?AGE . FILTER(?AGE >40) . \n"
				+ "{SELECT ?USER WHERE {\n" + "?MESSAGE sn:sent_by ?USER . ?USER2 sn:likes ?MESSAGE }}}\n";

		// Answer: Yes
		
		String test17 = "# ?USER2 sn:likes ?MESSAGE" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE {\n" + "?USER sn:nfollowers 200 . sn:antonio rdf:type sn:User }\n";

		// Answer: Yes
		
		String test18 = "# ?USER2 sn:likes ?MESSAGE" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE {\n" + "?USER sn:height '200'^^xsd:double . ?USER rdf:type sn:User }\n";

		// Answer: Yes
		
		String test19 = "# ?USER2 sn:likes ?MESSAGE" + "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n"
				+ "PREFIX owl: <http://www.w3.org/2002/07/owl#>\n" + "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n"
				+ "PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"
				+ "PREFIX sn: <http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#>\n"
				+ "SELECT ?USER WHERE {\n" + "?USER sn:height ?H . ?USER rdf:type sn:User . FILTER (?H>25) }\n";

		// Answer: Yes

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

		
		TSPARQL t = new TSPARQL(manager, manager_rdf, manager_owl, ontology, ont_rdf, ont_owl, dataFactory, df_rdf,
				df_owl, "C:/social-network-2019.owl");

		//t.SPARQL_CHECKING(test7);
		t.SPARQL_TESTING(test19, "USER", "http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#Tall");
		

	};
	 
	
	
}
