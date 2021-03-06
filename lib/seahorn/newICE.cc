#include "seahorn/ICE.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/GuessCandidates.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>
#include <boost/optional/optional.hpp>
#include <boost/tokenizer.hpp>
#include "boost/range/algorithm/reverse.hpp"
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>
#include <streambuf>

#include "ufo/Stats.hh"
#include "color.hh"

#include <chrono>
#include <ctime>


using namespace llvm;

static llvm::cl::opt<std::string> ICEInvDump("horn-ice-inv-dump", llvm::cl::desc("ICE Invariants Dump File:"), llvm::cl::init(""), llvm::cl::value_desc("filename"));
static llvm::cl::opt<std::string> C5ExecPath("horn-ice-c5-exec-path", llvm::cl::desc("C5 Executable File Path:"), llvm::cl::init(""), llvm::cl::value_desc("filename"));
static llvm::cl::opt<std::string> Z3ExecPath("horn-ice-z3-exec-path", llvm::cl::desc("Z3 Executable File Path:"), llvm::cl::init(""), llvm::cl::value_desc("filename"));
static llvm::cl::opt<unsigned> RuleSampleLen ("horn-rule-sample-length", cl::Hidden, cl::init (101));
static llvm::cl::opt<unsigned> RuleSampleWidth("horn-rule-sample-width", cl::Hidden, cl::init (1));
static llvm::cl::opt<std::string> SVMExecPath("horn-ice-svm-exec-path", llvm::cl::desc("SVM Executable File Path:"), llvm::cl::init(""), llvm::cl::value_desc("filename"));
static llvm::cl::opt<unsigned> SVMCParameter("horn-ice-svm-c-paramter", cl::Hidden, cl::init (100000));
static llvm::cl::opt<unsigned> SVMCoeffBound("horn-ice-svm-coeff-bound", cl::Hidden, cl::init (0));
static llvm::cl::opt<unsigned> SVMAHyperplane("horn-ice-svm-a-hyperplane", cl::Hidden, cl::init (0));
static llvm::cl::opt<unsigned> ICEMod("horn-ice-mod", cl::Hidden, cl::init (0));
static llvm::cl::opt<unsigned> ICESVMFreqPos("horn-ice-svm-call-freq-pos", cl::Hidden, cl::init (50));
static llvm::cl::opt<unsigned> ICESVMFreqNeg("horn-ice-svm-call-freq-neg", cl::Hidden, cl::init (100));
static llvm::cl::opt<unsigned> LC("horn-ice-lc", cl::Hidden, cl::init (0));
static llvm::cl::opt<unsigned> ICECatch("horn-ice-svm-caching", cl::Hidden, cl::init (0));
static llvm::cl::opt<unsigned> ICELocalStrengthen("horn-ice-local-strengthening", cl::Hidden, cl::init(0));
static llvm::cl::opt<unsigned> ICEOct("horn-ice-oct", cl::Hidden, cl::init(1));
static llvm::cl::opt<unsigned> ICEICE("horn-ice-ice", cl::Hidden, cl::init(0));
static llvm::cl::opt<unsigned> DebugLevel("debug-level", cl::desc("Debug Level: The higher the more information you get. Default = 5"), cl::init (5));

static llvm::cl::opt<bool> ShowDataSet("show-data-set", llvm::cl::desc ("Show the Data Set Information"), cl::init (false));
static llvm::cl::opt<bool> ShowC5NameFile("show-c5-name-file", llvm::cl::desc ("Show the names file to proceed by C5.0"), cl::init (false));
static llvm::cl::opt<bool> ShowC5IntervalFile("show-c5-interval-file", llvm::cl::desc ("Show the interval file to proceed by C5.0"), cl::init (false));
static llvm::cl::opt<bool> ShowC5DataFile("show-c5-data-file", llvm::cl::desc ("Show the data file to proceed by C5.0"), cl::init (false));
static llvm::cl::opt<bool> ShowC5HexDataFile("show-c5-hex-data-file", llvm::cl::desc ("Show the hex data file, corresponding to the data file proceeded by C5.0"), cl::init (false));
static llvm::cl::opt<bool> ShowC5JsonFile("show-c5-json-file", llvm::cl::desc ("Show the Json file output from C5.0"), cl::init (false));
static llvm::cl::opt<bool> ShowC5JsonStruct("show-c5-json-struct", llvm::cl::desc ("Show the Json file in structured form output from C5.0"), cl::init (false));

static llvm::cl::opt<unsigned> ColorEnable("color", cl::desc("Enable colored output or not"), cl::init (5));
#define USE_EXTERNAL 1
// #define USE_EXTERNAL 0

#define NEG_UNIFIED true

namespace seahorn
{
#define SAT_OR_INDETERMIN true
#define UNSAT false


#if USE_EXTERNAL
#define Solve(solver) callExternalZ3ToSolve(solver)
#define GetModel(solver) parseModelFromString(m_z3_model_str)
#define ModelToAttrValues(X) modelToAttrValues(m_z3_model, X)
#else
#define Solve(solver) solver.solve()
#define GetModel(solver) ZModel<EZ3> m = solver.getModel()
#define ModelToAttrValues(X) modelToAttrValues(m, X)
#endif


	/*ICEPass methods begin*/

	char ICEPass::ID = 0;

	bool ICEPass::runOnModule (Module &M)
	{
		LOG("ice", errs() << green << bold);
		LOG("ice", errs() << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
		LOG("ice", errs() << "-----------------------------------------------------------------------------------------------------------------------------------\n");
		LOG("ice", errs() << normal);
		HornifyModule &hm = getAnalysis<HornifyModule> ();

		LOG("ice-res", errs() << "Start ICE Pass\n");
		Stats::resume ("ICE inv");
		ICE ice(hm);
		ice.runICE();
		LOG("ice-res", errs() << "RUN ICE SUCCESSCULLY\n");
		Stats::stop ("ICE inv");

		return false;
	}

	void ICEPass::getAnalysisUsage (AnalysisUsage &AU) const
	{
		AU.addRequired<HornifyModule> ();
		AU.setPreservesAll();
	}

	/*ICEPass methods end*/

	/*ICE methods begin*/

	ExprVector getArgListFromRel(Expr rel) {
		ExprVector arg_list;
		for(int i=0; i<bind::domainSz(rel); i++)
		{
			Expr arg_i_type = bind::domainTy(rel, i);
			// Expr arg_i = bind::fapp(bind::constDecl(variant::tag(bind::fname(rel), variant::variant(i, mkTerm<std::string> ("v", rel->efac ()))), arg_i_type));
			// short name
			Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
			arg_list.push_back(arg_i);
		}
		return arg_list;
	}

	Expr getFappFromRel(Expr rel) {
		ExprVector arg_list = getArgListFromRel(rel);
		Expr fapp = bind::fapp(rel, arg_list);
		return fapp;
	}

	void getFappAndCandForRel(Expr rel, HornDbModel model, Expr& fapp, Expr& cand_app) {
		fapp = getFappFromRel(rel);
		cand_app = model.getDef(fapp);
	}

	void ICE::saveInvsToSmtLibFile()
	{
		auto &db = m_hm.getHornClauseDB();
		ZSolver<EZ3> solver(m_hm.getZContext());
		errs() << "======================================================\n";
		for(Expr rel : db.getRelations())
		{
			Expr fapp, cand_app;
			getFappAndCandForRel(rel, m_candidate_model, fapp, cand_app);
			errs() << bold << red << "HEAD: " << normal << blue << *fapp << "\n" << normal;
			errs() << bold << red << "CAND: " << normal << green << *cand_app << "\n" << normal;

			solver.assertExpr(mk<IMPL>(fapp, cand_app));
		}
		errs() << "======================================================\n";
		std::ofstream ofs(ICEInvDump.c_str());
		// solver.toSmtLib(errs());
		solver.toSmtLib(ofs);
	}

	void ICE::addInvCandsToProgramSolver()
	{
		LOG("ice", errs() << green << "========================== add inv cand to solver ===========================\n" << normal);
		auto &db = m_hm.getHornClauseDB();
		LOG("test", errs() << "pre_db---\n" << cyan << db << "\n" << normal);
		for(Expr rel : db.getRelations())
		{
			Expr fapp, cand_app;
			getFappAndCandForRel(rel, m_candidate_model, fapp, cand_app);
			LOG("candidates", errs() << bold << red << "HEAD: " << normal << blue << *fapp << "\n" << normal);
			LOG("candidates", errs() << bold << red << "CAND: " << normal << green << *cand_app << "\n" << normal);
			if(!isOpX<TRUE>(cand_app)) { 
				LOG("candidates", errs() << bold << green << "ADD CONSTRAINT\n" << normal); 
				LOG("candidates", errs() << "HEAD: " << blue << *fapp << "\n" << normal);
				LOG("candidates", errs() << "CAND: " << green << *cand_app << "\n" << normal);
				db.addConstraint(fapp, cand_app); 
			}
		}
		LOG("test", errs() << "post_db---\n" << cyan << db << "\n" << normal);
		LOG("ice", errs() << green << "========================== added inv cand to solver ===========================\n" << normal);
	}

	// Fixme. Helper function should be put into a util file
	std::vector<std::string> split_string(const std::string& str, const std::string& delimiter)
	{
		std::vector<std::string> strvec;

		std::string::size_type pos = 0, prev = 0;
		while ((pos = str.find(delimiter, prev)) != std::string::npos)
		{
			if (pos != prev)
				strvec.push_back(str.substr(prev, pos - prev));
			prev = pos + 1;
		}

		// To get the last substring (or only, if delimiter is not found)
		strvec.push_back(str.substr(prev));
		return strvec;
	}

	// after learning, set two fields
	// 	  m_svmattr_name_to_expr_map.insert(std::make_pair(attr_name_i, mknary<PLUS> (addargs)));
	// 	  m_svmattr_name_to_str_map.insert(std::make_pair(attr_name_i, attrstr));
	void ICE::svmLearn (Expr targetName) {
		LOGLINE("ice", errs() << "SVM Learn (target:" << *targetName << ") .\n");
		if (m_fact_predicates.count(targetName) > 0) {
			errs() << " this is a fact predicate, and thus the svm learning is skipped.\n";
			return;
		}
		// only care about the predicates in targetName
		auto &db = m_hm.getHornClauseDB();

		if (targetName == NULL && ICECatch == 0) {
			m_svmattr_name_to_expr_map.clear ();
			m_svmattr_name_to_str_map.clear ();
		}

		// for (Expr rel : m_rules) {
		for (Expr rel : db.getRelations()) {
			// LOGIT("ice", errs() << "SVM on predicate: " << cyan << bold << *(bind::fname(rel)) << normal << " --> ");
			if (m_fact_predicates.count(bind::fname(rel)) > 0) {
				// LOGIT("ice", errs() << " In Fact-Predicates, continue.\n");
				continue;
			}
			// LOGIT("ice", errs() << " NOT in Fact-Predicates, to learn it....\n");
			Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
			std::stringstream oss; oss << C5_rel_name;
			// oss = rel.C5_name
			if (targetName != NULL && ICECatch == 0) {
				if (targetName != bind::fname(rel)) continue;
				else { 
					// Remove previously found attributes.
					// If found the name in svmattr-name-to-expr:
					// 		erase it!
					// If found the name in svmattr-name-to-str:
					// 		erase it!
					ExprMap::iterator itr1 = m_svmattr_name_to_expr_map.begin();
					while (itr1 != m_svmattr_name_to_expr_map.end()) {
						std::stringstream ossB; ossB << itr1->first;
						if (ossB.str().find(oss.str()) != -1) { itr1 = m_svmattr_name_to_expr_map.erase(itr1); } 
						else { ++itr1; }
					}

					std::map<Expr, std::string>::iterator itr2 = m_svmattr_name_to_str_map.begin();
					while (itr2 != m_svmattr_name_to_str_map.end()) {
						std::stringstream ossB; ossB << itr2->first;
						if (ossB.str().find(oss.str()) != -1) { itr2 = m_svmattr_name_to_str_map.erase(itr2); } 
						else { ++itr2; }
					}
				}
			}

			// Excluse boolean variables for svm learning
			std::vector<int> exclusives;
			ExprVector arg_list;
			for(int i=0; i<bind::domainSz(rel); i++)
			{
				if (unknowns[rel][i]) { // Exclude unknowns from invariant inference.
					exclusives.push_back(i); continue;
				}
				Expr arg_i_type = bind::domainTy(rel, i);
				std::ostringstream oss; oss << arg_i_type;
				if (oss.str().compare("BOOL") == 0) { exclusives.push_back(i); continue; } 
				Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type)); 
				arg_list.push_back(arg_i);
			}

			LOG("ice", errs() << "SVM DATA FILES ARE GENERATING\n");
			int pn=0, nn=0;
			//generate .data file
			std::ofstream data_of(m_C5filename + ".svm.data");
			if(!data_of) return;

			for(auto it = m_cex_list.begin(); it!=m_cex_list.end(); ++it)
			{
				DataPoint dp = *it;
				if (dp.getPredName() == bind::fname(rel)) {
					std::string dpout = "";
					// output label
					if(m_pos_data_set.count(dp) != 0) { pn ++; dpout += "1"; } 
					else if(m_neg_data_set.count(dp) != 0) { pn ++; dpout += "-1"; }

					bool is_proper = true;
					// output attr
					int i = 0;
					for(Expr attr : dp.getAttrValues()) {
						// Not excluded as a boolean var.
						if (exclusives.empty() || std::find(exclusives.begin(), exclusives.end(), i) == exclusives.end()) { 
							std::string attr_str = attr->to_string();
							if (attr_str.find("bv") != std::string::npos) {
								int end = attr_str.find(':');
								std::string hex = attr_str.substr(1, end - 1);
								char * p;
								long n = strtol( hex.c_str(), &p, 16);
								if (*p!=0) {
									errs() << bred << "type error." << DataPointToStr(dp, empty, false) << " -> " << attr_str << " -> " << hex << normal << "\n";
									exit(-4);
								}
								// if (n>500000000 || n<-500000000)
								if (n>99999 || n<-99999)
									is_proper = false;
								attr_str = std::to_string(n);
							}
							dpout += " " + attr_str;
						}
						i++;
					}

					// errs() << bred << "### " << dpout << " isProper:" << is_proper << normal << "\n";
					if (is_proper) {
						data_of << dpout << "\n";
					}
				}
			}
			data_of.close();
			LOG("ice", errs() << "SVM DATA FILES ARE GENERATED\n");

			// Call SVM to learn invariants
			// call SVM, output the result into buf, output "attr" into FromCmd.attr
			FILE *fp;
			std::string command = SVMExecPath +
				" -c " + std::to_string(SVMCParameter) +
				" -t " + std::to_string(SVMCoeffBound) +
				" -a " + std::to_string(SVMAHyperplane) +
				" -v " + std::to_string(arg_list.size()) +
				" -p " + std::to_string(pn) +
				" -n " + std::to_string(nn) +
				" -g " + std::to_string(LC) +
				" -f " + oss.str() + " " +
				m_C5filename + ".svm.data";

			LOG("ice", errs() << "Call SVM: " << command << "\n");
			if((fp = popen(command.c_str(), "r")) == NULL) { LOG("ice", errs() << "popen error!\n"); perror("popen failed!\n"); return; }
			LOG("ice", errs() << "call svm returns!\n");
			pclose(fp);
			n_svm_calls ++;

			std::ifstream if_svm(m_C5filename + ".attr");
			std::ostringstream svm_buf;
			char ch;
			while(svm_buf && if_svm.get(ch)) { svm_buf.put(ch); }
			if_svm.close();
			std::string svmattr_string = svm_buf.str();
			std::vector<std::string> lines = split_string (svmattr_string, "\n");
			LOG("ice", errs() << "svmattr_string: " << yellow << svmattr_string << normal);

			// Expr zero = mkTerm<mpz_class>(0, rel->efac());
			// mk<GEQ>(mknary<PLUS> (addargs), zero)));
			int index = ICECatch == 0 ? 0 : m_svmattr_name_to_expr_map.size();  //0;
			bool dt_learning = true;
			for (auto line= lines.begin(); line!= lines.end(); line++) {
				std::string attr = *line;
				if (attr.compare("true") != 0 && attr.compare("false") != 0) {
					ExprVector addargs;
					std::ostringstream attross;
					std::vector<std::string> thetas = split_string (attr, " ");
					for (int i = 1; i < thetas.size(); i++) {
						int coef = atoi(thetas[i].c_str());
						if (coef == 0) continue; //if (coef != 1 && coef != -1) nonOctagon = true;

						Expr c = mkTerm<mpz_class>(coef, rel->efac());
						if (Bounded)
							addargs.push_back (mk<MULT> (c, mk<BV2INT>(arg_list.at(i-1))));
						else
							addargs.push_back (mk<MULT> (c, arg_list.at(i-1)));

						attross << "(" << thetas[i].c_str() << "*" << C5_rel_name << "!" << arg_list.at(i-1) << ")+";
						LOG("SVM", llvm::errs() << bold << red << "(" << thetas[i].c_str() << "*" << C5_rel_name << "!" << arg_list.at(i-1) << ")+" << normal);
					}

					if (addargs.size () > 1 /*&& nonOctagon*/) {
						Expr arg_i_type = sort::intTy(rel->efac());
						Expr arg_i = bind::fapp(bind::constDecl(variant::variant(index, mkTerm<std::string> ("SVM", rel->efac ())), arg_i_type));
						Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
						std::string attr_name_str = attross.str(); attr_name_str = attr_name_str.substr(0, attr_name_str.length()-1); // remove the last "+"
						m_svmattr_name_to_expr_map.insert(std::make_pair(attr_name_i, mknary<PLUS> (addargs)));
						m_svmattr_name_to_str_map.insert(std::make_pair(attr_name_i, attr_name_str));
						LOG("ice", errs() << bold << red << "SVM inferred a hyperlane: " << attr_name_str << "\n" << normal);
					}
				}
				index++;
			}
		}
	}


	// change m_rel_to_c5_rel_name_map and m_c5_rel_name_to_rel_map
	void ICE::setupC5() {
		m_C5filename = "FromCmd";

		//convert predicate names to the name format of C5
		auto &db = m_hm.getHornClauseDB();
		int rel_index = 0;
		for(Expr rel : db.getRelations()) /* relation is predicate*/
		{
			Expr C5_rel_name = variant::variant(rel_index, mkTerm<std::string>(std::string("PRED"), rel->efac()));
			m_rel_to_c5_rel_name_map.insert(std::make_pair(bind::fname(rel), C5_rel_name));
			m_c5_rel_name_to_rel_map.insert(std::make_pair(C5_rel_name, bind::fname(rel)));
			rel_index ++;
		}

		//consider whether collecting integer constants (for modular operation) in the rule is useful.
		if (ICEMod) {
			extractConstants(db);
			if (ruleConstants.size() > 0) {
				LOGLINE("const", errs() << " inspect constants in Modulo operations in CHC \n");
				for (auto i : ruleConstants) {
					LOGIT("const", errs() << " -> " << i << "\t"); 
				}
				LOGLINE("const", errs() << "\n end of constants\n"); 
			}
		}
		//consider unknowns which are definitely not useful in invariant inference.
		extractUnknowns(db);

		//print the map from predicate name to C5-form predicate name
		LOGDP("ice", errs() << lblue << "                    REL NAME TO C5 NAME MAP\n" << normal);
		LOGDP("ice", errs() << lblue << "------------------------------------------------------------\n" << normal);
		LOGDP("ice", errs() << lblue << "| " << normal << "Relation in CHC            " << lblue << "||" << normal << " Relation in C5            " << lblue << "|\n" << normal);
		for(auto it = m_rel_to_c5_rel_name_map.begin(); it != m_rel_to_c5_rel_name_map.end(); ++it) 
		{
			int itemsize = 25;
			std::ostringstream ss; 
			ss << *(it->first); 
			int len = ss.str().length();
			while (itemsize-- >= len) { ss << " "; }
			ss << " || " << *(it->second); 
			itemsize = 25;
			len = ss.str().length() - itemsize - 4;
			while (itemsize-- >= len) { ss << " "; }
			LOGDP("ice", errs() << lblue << "| " << ss.str() << " |\n" << normal);
		}
		LOGDP("ice", errs() << lblue << "------------------------------------------------------------\n" << normal);
	}

	void outputFileContent(std::string filename, int linelength = 54) {
		if (DebugLevel<=4) 
			return;
		std::ifstream _if(filename); 
		std::string str((std::istreambuf_iterator<char>(_if)), std::istreambuf_iterator<char>());
		int endlpos = str.find("\n");
		int last_endlpos = -1;
		while (endlpos != std::string::npos) {
			std::string pre_str = "| ";
			std::string post_str = " |";
			int nspace = linelength - 4  - (endlpos - last_endlpos);
			while (nspace-->0)
				post_str = " " + post_str;
			str = str.insert(endlpos, post_str);
			str = str.insert(last_endlpos+1, pre_str);
			last_endlpos = str.find("\n", endlpos);
			endlpos = str.find("\n", last_endlpos+1);
		}
		// errs() << bold << mag << "|------------- " << filename << " --------------";
		errs() << bold << mag << "-------------- " << filename << " --------------";
		int len = filename.size() + 32;
		while (len++<linelength) errs() << "-";
		// errs() << "|\n" << str;
		errs() << "-\n" << str;
		std::string end = "";
		while (--linelength>0)
			end += "-";
		errs() << end << "\n" << normal;
		//errs() << "|--------------------- END -------------------------|\n" << normal;
	}

	//Set .names file and .interval file
	//Only set up for the predicate we want to re-Learn.
	void ICE::initC5(ExprVector targets)
	{ 
		auto &db = m_hm.getHornClauseDB();
		m_attr_name_to_expr_map.clear();
		m_pred_name_to_expr_map.clear();

		std::ofstream names_of(m_C5filename + ".names"); if(!names_of) return;
		names_of << "invariant.\n";

		std::ofstream intervals_of(m_C5filename + ".intervals"); if(!intervals_of) return;

		int lowerInterval = 2;
		int upperInterval = 2;

		//first attribute is the predicate names
		names_of << "$pc: ";
		int counter = 0;
		for(Expr rel : db.getRelations()) {
			if(std::find(targets.begin(), targets.end(), bind::fname(rel)) != targets.end()) {
				Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
				if(counter == targets.size()-1) { names_of << *C5_rel_name << ".\n"; }
				else { names_of << *C5_rel_name << ","; }
				counter++;
			}
		}

		//each argument of each predicate is an attribute
		for(Expr rel : db.getRelations())
		{
			errs() << "Predicate: " << *rel << "\n";
			if(std::find(targets.begin(), targets.end(), bind::fname(rel)) != targets.end()) {
				Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
				for(int i=0; i<bind::domainSz(rel); i++)
				{
					Expr arg_i_type = bind::domainTy(rel, i);
					Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
					Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
					LOG("ice", errs() << "check --" << *arg_i_type << " " << *attr_name_i << ": ");
					if(isOpX<BVSORT>(bind::domainTy(rel, i)) || isOpX<INT_TY>(bind::domainTy(rel, i)) || isOpX<BOOL_TY>(bind::domainTy(rel, i)))
					{
						LOG("ice", errs() << green << "GOOD, in int/bv/bool TYPE!\n" << normal);
						if (unknowns[rel][i]) // Exclude unknowns from invariant inference.
						{
							LOG("ice", errs() << red "        --> unknown, thus skip\n" << normal);
							continue;
						}
						Expr arg_i_type = bind::domainTy(rel, i);
						Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
						Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
						m_attr_name_to_expr_map.insert(std::make_pair(attr_name_i, arg_i));
						names_of << attr_name_i << ": continuous.\n";
						upperInterval ++;
					}
					else { 
						LOG("ice", errs() << red << "BAD, not in int/bv/bool TYPE!\n" << normal);
					}
				}
				//implicit attributes which have the form x % n.
				if (ICEMod > 0 && !ruleConstants.empty()) {
					for(int i=0; i<bind::domainSz(rel); i++)
					{ // Exclude unknowns from invariant inference.
						if (unknowns[rel][i]) continue;
						for (int cons : ruleConstants) {
							// if(isOpX<INT_TY>(bind::domainTy(rel, i)) || (isOpX<BV_TY>(bind::domainTy(rel, i))))
							if(isOpX<INT_TY>(bind::domainTy(rel, i)) || (isOpX<bv::BvSort>(bind::domainTy(rel, i))))
							{
								Expr arg_i_type = bind::domainTy(rel, i);
								Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
								Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
								names_of << attr_name_i << "mod" << cons << ":= (" << attr_name_i << " % " << cons << " + " << cons << ") % " << cons << ".\n";
								upperInterval ++;
							}
						}
					}
				}
				//implicit attributes which have the form x1 +/- x2
				if (ICEOct) {
					for(int i=0; i<bind::domainSz(rel); i++)
					{ 
						if (unknowns[rel][i]) continue; // Exclude unknowns from invariant inference.
						for(int j=i+1; j<bind::domainSz(rel); j++)
						{ 
							if (unknowns[rel][j]) continue; // Exclude unknowns from invariant inference.
							if((isOpX<INT_TY>(bind::domainTy(rel, i)) && isOpX<INT_TY>(bind::domainTy(rel, j))) 
									|| (isOpX<bv::BvSort>(bind::domainTy(rel, i))))
								// || (isOpX<BV_TY>(bind::domainTy(rel, i)) && isOpX<BV_TY>(bind::domainTy(rel, j))))
							{
								Expr arg_type = bind::domainTy(rel, i);
								Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_type));
								Expr arg_j = bind::fapp(bind::constDecl(variant::variant(j, mkTerm<std::string> ("v", rel->efac ())), arg_type));
								Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
								Expr attr_name_j = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_j)));
								names_of << attr_name_i << "+" << attr_name_j << ":= " << attr_name_i << " + " << attr_name_j << ".\n";
								names_of << attr_name_i << "-" << attr_name_j << ":= " << attr_name_i << " - " << attr_name_j << ".\n";
								upperInterval += 2;
							}
						}
					}
				}
				// atrributes found by SVM -- which must be realted to C5_rel_name
				std::ostringstream ossR; ossR << C5_rel_name;
				for(std::map<Expr, std::string>::iterator it = m_svmattr_name_to_str_map.begin(); it!= m_svmattr_name_to_str_map.end(); ++it)
				{
					std::ostringstream ossA; ossA << *(it->first);
					if (ossA.str().find(ossR.str()) != std::string::npos) {
						// This is ineed realted to C5_rel_name
						names_of << *(it->first) << ":= " << (it->second) << ".\n";
						upperInterval ++;
					}
				}

				errs() << "lowerinterval: " << lowerInterval << "  upperInterval: " << upperInterval << "\n";
				std::string interval_line;
				if(bind::domainSz(rel) == 0) { interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval) + "\n"; }
				else { interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval - 1) + "\n"; }
				errs() << "<><> " << interval_line;
				intervals_of << interval_line;
				lowerInterval = upperInterval;
				upperInterval = lowerInterval;
			}
		}

		// names_of << "PRED_FAKE!v_0: continuous.\n";
		names_of << "invariant: true, false.\n";
		names_of.close();
		intervals_of.close();
		if (ShowC5NameFile)
			outputFileContent(m_C5filename + ".names");
		if (ShowC5IntervalFile)
			outputFileContent(m_C5filename + ".intervals");
	}

	std::string ptreeToString(boost::property_tree::ptree pt) {
		// return "Ignore.";
		std::stringstream ss;
		boost::property_tree::json_parser::write_json(ss, pt);
		return ss.str();
	}


	void ICE::C5learn(ExprVector targets)
	{
		if (targets.size() == 0) return;
		// at least there are two targets
		if (targets.size() == 1) {
			Expr to_add;
			for (auto e : m_fact_predicates) {
				std::string estr = e->to_string();
				if (estr.find("error") == std::string::npos) {
					to_add = e;
					break;
				}
			}
			errs() << " TO add: " << *to_add << "\n";
			targets.push_back(to_add);
		}
		// errs() << "before C5Learn\n" << cyan << m_candidate_model << "\n" << normal;
		errs() << bblue << "---------------------C5Learn-------------------" << normal << " targets[" << targets.size() << "]: ";
		for (int i = 0; i < targets.size(); i++) errs() << bold << blue << *targets[i] << normal << " ";
		errs() << normal << "\n";
		errs() << DataSetToStr() << "\n";

		// ExprVector real_targets;
		for (auto target : targets) {
			if (m_fact_predicates.count(target) == 0) {
				// real_targets.push_back(target);
				errs() << " check if knowns in [" << *target << "] is more than 1? \n";
				assert(m_pred_knowns_count.count(target) >= 1);
				if (m_pred_knowns_count[target] > 1) {
					errs() << " YES! Use SVM to generate features\n";
					svmLearn(target);
				}
				else 
				{
					errs() << " NO! Hence skip SVM Learning \n";
				}
			}
			else 
			{
				errs() << " predicate is fact! [" << *target << "] \n";
			}
		}
		// targets = real_targets;
		initC5(targets); // Set .names file and .interval file
		generateC5DataAndImplicationFiles(targets);
		LOG("ice", errs() << "DATA & IMPL FILES ARE GENERATED\n");

		// call C50, output to .json file
		FILE *fp;
		std::string command = C5ExecPath + " -I 1 -m 1 -f " + m_C5filename;
		//std::string command = "/home/chenguang/Desktop/C50-ICE/C50/c5.0dbg -I 1 -m 1 -f " + m_C5filename;
		errs() << blmag << "---> " << command << normal << "\n";
		if((fp = popen(command.c_str(), "r")) == NULL) { perror("popen failed!\n"); return; }
		pclose(fp);

		//parse the .json file to ptree
		std::ifstream if_json(m_C5filename + ".json");
		std::ostringstream json_buf; char ch; while(json_buf && if_json.get(ch)) { json_buf.put(ch); } if_json.close();
		std::string json_string = json_buf.str();
		if (ShowC5JsonFile) errs() << "json: " << cyan << json_string << "\n" << normal;

		LOG("ice", errs() << " >>> convert json to ptree: \n");
		boost::property_tree::ptree pt;
		std::stringstream ss(json_string);
		try { boost::property_tree::json_parser::read_json(ss, pt); }
		catch(boost::property_tree::ptree_error & e) { LOG("ice", errs() << "READ JSON ERROR!\n"); return; }
		if (ShowC5JsonStruct)
			LOGLINE("ice", errs() << " <<< convert json to ptree (structured json format): \n" << mag << ptreeToString(pt) << "\n");

		//parse ptree to invariant format
		LOGLINE("ice", errs() << " >>> convert ptree to inv. \n");
		/* m_candidate_model = */ convertPtreeToInvCandidate(pt, targets);
		LOGLINE("ice", errs() << " <<< convert ptree to inv. \n");
		errs() << CandidateToStr() << "\n";
	}


	std::string ICE::DataPointToStr(DataPoint p, ExprVector targets, bool valueOnly)
	{
		auto &db = m_hm.getHornClauseDB();
		Expr pred_name = p.getPredName();
		Expr C5_pred_name = m_rel_to_c5_rel_name_map.find(pred_name)->second;
		std::ostringstream oss; 
		if (valueOnly == false)
			oss << "[" << pred_name << "] ";
		oss << C5_pred_name;

		for(Expr rel : db.getRelations()) {
			// LOGIT("ice", errs() << "InitC5 on predicate: " << cyan << bold << *(bind::fname(rel)) << normal << " --> ");
			if (m_fact_predicates.count(bind::fname(rel)) > 0) {
				// LOGIT("ice", errs() << " In Fact-Predicates, continue.\n");
				continue;
			}
			// LOGIT("ice", errs() << " Not in Fact-Predicates, proceed to the next step.\n");
			if(bind::fname(rel) == pred_name) {
				int i = 0;
				for(Expr attr : p.getAttrValues()) {
					if (!unknowns[rel][i]) { oss << "," << *attr; }
					i++;
				}
			} else if (std::find(targets.begin(), targets.end(), bind::fname(rel)) != targets.end()) {
				for(int i=0; i<bind::domainSz(rel); i++) { if (!unknowns[rel][i]) oss << ",?"; }
			}
		}
		return oss.str();
	}


	std::string ICE::DataSetToStr(bool mustprint) {
		std::ostringstream oss; 
		if (!ShowDataSet && !mustprint)
			return oss.str();

		oss << blue << "===================================================================\n" << normal; 
		oss << green << "|---------------------  POS DATA SET -----------------------" << "(" << m_pos_data_set.size() << ")" << normal << "\n"; 
		for (auto dp: m_pos_data_set) {
			// if (std::find(m_must_pos_data_set.begin(), m_must_pos_data_set.end(), dp) != m_must_pos_data_set.end()) oss << bold;
			oss << green << "| " << DataPointToStr(dp) << normal << "\n"; 
		}
		oss << green << bold << "|zzzzzzzzzzzzzzzzzzzzz  MUST POS DATA zzzzzzzzzzzzzzzzzzzzzzz" << "(" << m_must_pos_data_set.size() << ")" << normal << "\n"; 
		for (auto dp: m_must_pos_data_set) {
			oss << green << bold << "| " << DataPointToStr(dp) << normal << "\n"; 
		}

		oss << red <<   "|---------------------  NEG DATA SET -----------------------" << "(" << m_neg_data_set.size() << ")" << normal << "\n"; 
		for (auto dp: m_neg_data_set) {
			// if (std::find(m_must_neg_data_set.begin(), m_must_neg_data_set.end(), dp) != m_must_neg_data_set.end()) oss << bold;
			oss << red << "| " << DataPointToStr(dp) << normal << "\n"; 
		}
		oss << red << bold << "|zzzzzzzzzzzzzzzzzzzzz  MUST NEG DATA zzzzzzzzzzzzzzzzzzzzzzz" << "(" << m_must_neg_data_set.size() << ")" << normal << "\n"; 
		for (auto dp: m_must_neg_data_set) {
			oss << red << bold << "| " << DataPointToStr(dp) << normal << "\n"; 
		}

		oss << blue <<  "|---------------------  IMPL DATA SET ----------------------" << "(" << m_impl_pair_set.size() << ")" << normal << "\n"; 
		for (auto data_chain : m_impl_data_set) {
			for (auto dp : data_chain) {
				oss << blue << "| " << DataPointToStr(dp) << normal << "\n"; 
			}
			oss << normal << "| ---next---data-chain----\n"; 
		}
		/*
		if (ICEICE) {
			oss << blue <<  "|---------------------  IMPL DATA SET ----------------------" << "(" << m_impl_pair_set.size() << ")" << normal << "\n"; 
			for (auto dp: m_impl_pair_set)
				oss << blue << "| " << DataPointToStr(dp.first) << " -> " << DataPointToStr(dp.second) << normal << "\n"; 
		}
		*/
		oss << blue << "===================================================================\n" << normal; 
		return oss.str();
	}

	std::string ICE::CandidateToStr() {
		auto &db = m_hm.getHornClauseDB();
		//print the invariant map after this learning round
		std::ostringstream oss; 
		oss << yellow << "^^^^^^^^^^^^^^^^^^^ CANDIDATE MODEL ^^^^^^^^^^^^^^^^^^^^^\n" << normal;
		for(Expr rel : db.getRelations()) {
			// LOGIT("ice", errs() << red << " relation : " << *rel << "\n" << normal);
			Expr fapp, cand_app;
			getFappAndCandForRel(rel, m_candidate_model, fapp, cand_app);
			oss << green << *fapp << normal << " : " << blue << *cand_app << normal << "\n";
		}
		return oss.str();
	}

	std::string ICE::DataPointToPlainStr(DataPoint& dp, ExprVector targets) {
		std::string dpstr = DataPointToStr(dp, targets);
		errs() << "datapoint: " << dpstr << "\n";
		if (Bounded) {
			int start1, start2 = dpstr.find(":bv");
			int end1, end2;
			// if (start2 != std::string::npos) 
			// errs() << "datapoint: " << dpstr << blue << " bvdata >> convert to integer format >> " << normal;
			while (start2 != std::string::npos) {
				end2 = dpstr.find(")", start2);
				end2 = dpstr.find(")", end2)+1;
				start1 = dpstr.rfind("(", start2);
				end1 = start1+1;
				// errs() << red << "bv data: " << bold << dpstr << normal 
				// << " range [" << start1 << ", " << end1 << "], [" << start2 << ", " << end2 << "] ---> ";
				std::string bvstr = dpstr.substr(end1, start2-end1);
				if (bvstr.find("0x") != -1) {
					// errs() << red << "bv value: " << bold << bvstr << "\n" << normal;
					int bvint = std::stol (bvstr,nullptr,16);
					// errs() << red << " -> int:" << bvint; 
					bvstr = std::to_string(bvint);
					// errs() << " str:" << bvstr << "\n" << normal;
				}
				dpstr = dpstr.replace(start1, end2 + 1 - start1, bvstr); 
				// errs() << " --> " << dpstr << "\n";
				start2 = dpstr.find(":bv");
			}
		}
		return dpstr;
	}


	void ICE::generateC5DataAndImplicationFiles(ExprVector targets)
	{
		/*
		errs() << " generate C5 Data File -----------targets:";
		for (auto target: targets)
			errs() << "  " << *target;
		errs() << "\n";
		*/
		// errs() << DataSetToStr() << "\n";
		//generate .data file
		std::ofstream data_of(m_C5filename + ".data");
		std::ofstream data_hex_of(m_C5filename + ".hex.data");
		if(!data_of) return;
		if(!data_hex_of) return;

		std::string label = "true";
		for(auto dp : m_must_pos_data_set) {
			if (std::find(targets.begin(), targets.end(), dp.getPredName()) != targets.end()) {
				data_of << DataPointToPlainStr(dp, targets) << "," << label << "\n";
				data_hex_of << DataPointToStr(dp, targets) << "," << label << "\n";
			}
		}

		label = "false";
		for(auto dp : m_must_neg_data_set) {
			if (std::find(targets.begin(), targets.end(), dp.getPredName()) != targets.end()) {
				data_of << DataPointToPlainStr(dp, targets) << "," << label << "\n";
				data_hex_of << DataPointToStr(dp, targets) << "," << label << "\n";
			}
		}

		data_of.close();
		data_hex_of.close();
		if (ShowC5DataFile)
			outputFileContent(m_C5filename + ".data"); 
		if (ShowC5HexDataFile)
			outputFileContent(m_C5filename + ".hex.data", 100); 

		//generate .implications file
		if (ICEICE) {
			std::ofstream implications_of(m_C5filename + ".implications");
			if(!implications_of) return;

			for(std::pair<DataPoint, DataPoint> impl_pair : m_impl_pair_set) {
				DataPoint start_point = impl_pair.first;
				if (std::find(targets.begin(), targets.end(), start_point.getPredName()) != targets.end()) {
					std::map<DataPoint, int>::iterator it = m_data_point_to_index_map.find(start_point);
					assert(it != m_data_point_to_index_map.end());
					int start_index = it->second;

					DataPoint end_point = impl_pair.second;
					std::map<DataPoint, int>::iterator itr = m_data_point_to_index_map.find(end_point);
					assert(itr != m_data_point_to_index_map.end());
					int end_index = itr->second;

					implications_of << start_index << " " << end_index << "\n";
					LOG("ice", errs()<< "implication: " <<  start_index << " " << end_index << "\n");
				}
			}

			implications_of.close();
			outputFileContent(m_C5filename + ".implications"); 
		}
	}


	void ICE::convertPtreeToInvCandidate(boost::property_tree::ptree pt, ExprVector targets)
	{
		auto &db = m_hm.getHornClauseDB();
		//if only have the root node
		Expr True = mk<TRUE>(db.getExprFactory());
		Expr False = mk<FALSE>(db.getExprFactory());
		if(pt.get<std::string>("children") == std::string("null")) {
			LOG("ice", errs() << "PT HAS NO CHILDREN\n");
			Expr candidate;
			if(pt.get<std::string>("classification") == "true" || pt.get<std::string>("classification") == "True")
				candidate = True;
			if(pt.get<std::string>("classification") == "false" || pt.get<std::string>("classification") == "False")
				candidate = False;
			for(Expr rel : db.getRelations()) {
				if (m_fact_predicates.count(bind::fname(rel)) > 0) {
					continue;
				}
				Expr fapp = getFappFromRel(rel);
				m_candidate_model.addDef(fapp, candidate);
				LOG("ice", errs() << *fapp << " ---CANDIDATE---> " << *candidate << "\n");
			}
			return;
		}

		boost::property_tree::ptree children = pt.get_child("children");
		auto rels_it = db.getRelations().begin();
		for(auto child_it : children) {
			while (std::find(targets.begin(), targets.end(), bind::fname(*rels_it)) == targets.end()) {
				rels_it++;
				assert (rels_it != targets.end());
			}

			Expr rel = *rels_it;
			if (m_fact_predicates.count(bind::fname(rel)) > 0) {
				continue;
			}
			Expr candidate;
			Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
			std::ostringstream oss; oss << C5_rel_name;
			// LOGLINE("ice", errs() << "target: " << oss.str() << "\n");

			boost::property_tree::ptree sub_pt = child_it.second;
			// LOGLINE("ice", errs() << "working on ptree-----------------------------\n " << cyan << ptreeToString(sub_pt) << "\n" << normal);
			if(sub_pt.get<std::string>("children") == std::string("null")) {
				// errs() << bold << red << "branch 0\n" << normal;
				if(sub_pt.get<std::string>("classification") == "true" || sub_pt.get<std::string>("classification") == "True")
					candidate = True;
				if(sub_pt.get<std::string>("classification") == "false" || sub_pt.get<std::string>("classification") == "False")
					candidate = False;
			} else {
				std::list<Expr> stack;
				stack.push_back(mk<TRUE>(db.getExprFactory()));
				std::list<std::list<Expr>> final_formula = constructFormula(stack, sub_pt);
				ExprVector disjunctions;
				for(std::list<std::list<Expr>>::iterator disj_it = final_formula.begin(); disj_it != final_formula.end(); ++disj_it) {
					ExprVector conjunctions;
					for(std::list<Expr>::iterator conj_it = (*disj_it).begin(); conj_it != (*disj_it).end(); ++conj_it)
					{
						if (isOpX<TRUE>(*conj_it))
							continue;
						if (isOpX<FALSE>(*conj_it)) {
							conjunctions.clear();
							break;
						}
						conjunctions.push_back(*conj_it);
					}
					Expr disjunct;
					if (conjunctions.size() <= 0) continue;
					else if (conjunctions.size() == 1)  disjunct = conjunctions[0];
					else disjunct = mknary<AND>(conjunctions.begin(), conjunctions.end());
					disjunctions.push_back(disjunct);
				}
				if(disjunctions.size() <= 0) candidate = mk<TRUE>(db.getExprFactory());
				else if(disjunctions.size() == 1) candidate = disjunctions[0];
				else candidate = mknary<OR>(disjunctions.begin(), disjunctions.end());
				// errs() << "condidate: " << *candidate << "\n";
			}

			Expr fapp = getFappFromRel(rel);
			m_candidate_model.addDef(fapp, candidate);
			LOG("ice", errs() << *fapp << " ---CANDIDATE---> " << *candidate << "\n");
			rels_it++;
		}
	}


	std::list<std::list<Expr>> ICE::constructFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt)
	{
		Expr decision_expr;
		std::list<std::list<Expr>> final_formula;
		auto &db = m_hm.getHornClauseDB();
		LOG("ice", errs() << cyan << bold << "Construct formula for ptree ---------------\n " << mag << ptreeToString(sub_pt) << normal);
		if (Bounded) {
			LOG("ice", errs() << red << "--------------- **  BOUNED  ** -----------------\n " << normal);
		} else {
			LOG("ice", errs() << red << "--------------- ** UNBOUNED ** -----------------\n " << normal);
		}
		//leaf node
		if(sub_pt.get<std::string>("children") == std::string("null"))
		{
			LOG("ice", errs() << "LEAF NODE\n");
			if(sub_pt.get<std::string>("classification") == "true" || sub_pt.get<std::string>("classification") == "True") {
				std::list<Expr> new_conjunct = stack;
				final_formula.push_back(new_conjunct);
				return final_formula;
			}
			else if(sub_pt.get<std::string>("classification") == "false" || sub_pt.get<std::string>("classification") == "False") {
				return final_formula;
			}
		}
		//internal node
		else 
		{
			LOG("ice", errs() << "INTERNAL NODE\n");
			std::string attr_name = sub_pt.get<std::string>("attribute");
			LOG("ice", errs() << "CUT ATTRIBUTE: " << attr_name << "\n");
			int cut = sub_pt.get<int>("cut");
			Expr threshold = mkTerm (mpz_class (std::to_string(cut)), db.getExprFactory());
			// int upper = sub_pt.get<int>("upper");
			// int lower = sub_pt.get<int>("lower");
			// LOGIT("ice", errs() << " CutExpr[" << *threshold << "] cut:" << cut << " upper:" << upper << " lower:" << lower << "\n");


			if(attr_name.find("+") != -1) { 
				LOG("ice", errs() << cyan << " + plus attr: \n" << normal);
				decision_expr = plusAttrToDecisionExpr(sub_pt, attr_name); } 
			else if(attr_name.find("-") != -1) { 
				LOG("ice", errs() << cyan << " + minus attr: \n" << normal);
				decision_expr = minusAttrToDecisionExpr(sub_pt, attr_name); } 
			else if (attr_name.find("mod") != -1) { 
				LOG("ice", errs() << cyan << " + mod attr: \n" << normal);
				decision_expr = modAttrToDecisionExpr(sub_pt, attr_name); } 
			else if (attr_name.find("SVM") != -1) {
				LOG("ice", errs() << cyan << " + svm attr: \n" << normal);
				Expr attr_expr;
				for(ExprMap::iterator it = m_svmattr_name_to_expr_map.begin(); it!= m_svmattr_name_to_expr_map.end(); ++it) {
					std::ostringstream oss; oss << *(it->first);
					if(oss.str() == attr_name) { attr_expr = it->second; }
				}
				if(isOpX<GEQ>(attr_expr)) {
					decision_expr = mk<NEG>(attr_expr);
					assert(cut == 0);
				} else if(isOpX<PLUS>(attr_expr)) {
					decision_expr = mk<LEQ>(attr_expr, threshold);
				}
			}
			else
			{ // not svm
				LOG("ice", errs() << cyan << " + variable (not svm) attr: \n" << normal);

				Expr attr_expr;
				for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it) {
					std::ostringstream oss; oss << *(it->first);
					if(oss.str() == attr_name) { attr_expr = it->second; break; }
				}
				LOG("ice", errs() << blue << " << attr_expr: " << *attr_expr << " >>" << normal);
				if(bind::isBoolConst(attr_expr) /*|| isOpX<GEQ>(attr_expr)*/) {
					LOG("ice", errs() << blue << "  --> bool const \n" << normal);
					decision_expr = mk<NEG>(attr_expr);
					assert(cut == 0);
				} else if(bind::isIntConst(attr_expr) /*|| isOpX<PLUS>(attr_expr)*/) {
					LOG("ice", errs() << blue << "  --> int const , cut: " << cut << "\n" << normal);
					decision_expr = mk<LEQ>(attr_expr, threshold);
				} else if(bind::isBvConst(attr_expr) /*|| isOpX<PLUS>(attr_expr)*/) {
					LOG("ice", errs() << blue << "  --> bv const , cut: " << cut << "\n" << normal);
					attr_expr = mk<BV2INT>(attr_expr);
					decision_expr = mk<LEQ>(attr_expr, threshold);
				} else {
					LOGIT("ice", errs() << "DECISION NODE TYPE WRONG!\n");
					return final_formula;
				}
			}
			LOG("ice", errs() << bold << green << "decision expr: " << *decision_expr << "\n" << normal);
			//assert(sub_pt.children().size() == 2);
			stack.push_back(decision_expr);
			boost::property_tree::ptree::assoc_iterator child_itr = sub_pt.get_child("children").ordered_begin();
			std::list<std::list<Expr>> final_formula_left = constructFormula(stack, child_itr->second);
			stack.pop_back();
			stack.push_back(mk<NEG>(decision_expr));
			std::list<std::list<Expr>> final_formula_right = constructFormula(stack, (++child_itr)->second);
			stack.pop_back();
			final_formula_left.insert(final_formula_left.end(), final_formula_right.begin(), final_formula_right.end());
			return final_formula_left;
		}
		// should not be here.
		LOGLINE("ice", errs() << bred << "should not be here." << normal << "\n");
		exit(-4);
		return final_formula;
	}


	//given an attribute which is x+y, return the expr
	Expr ICE::plusAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name)
	{
		typedef boost::tokenizer< boost::char_separator<char>> t_tokenizer;
		boost::char_separator<char> sep("+");
		t_tokenizer tok(attr_name, sep);
		std::string left_name = *(tok.begin());
		std::string right_name = *(++tok.begin());
		Expr left_expr, right_expr;
		for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it) {
			std::ostringstream oss; oss << *(it->first);
			if(oss.str() == left_name) left_expr = it->second;
			if(oss.str() == right_name) right_expr = it->second;
		}
		if (Bounded) {
			if(!bind::isBvConst(left_expr) || !bind::isBvConst(right_expr)) 
				LOGLINE("ice", errs() << "OPERAND TYPE WRONG (not bv)!\n");
			left_expr = mk<BV2INT>(left_expr);
			right_expr = mk<BV2INT>(right_expr);
		} else {
			if(!bind::isIntConst(left_expr) || !bind::isIntConst(right_expr))
				LOGLINE("ice", errs() << "OPERAND TYPE WRONG! (not int)\n");
		}
		int cut = sub_pt.get<int>("cut");
		Expr threshold = mkTerm<mpz_class>(cut, left_expr->efac());
		// Expr c = mkTerm<mpz_class>(1, left_expr->efac());
		// Expr decision_expr = mk<LEQ>(mk<PLUS>(mk<MULT>(c, left_expr), mk<MULT>(c, right_expr)), threshold);
		Expr decision_expr = mk<LEQ>(mk<PLUS>(left_expr, right_expr), threshold);
		return decision_expr;
	}

	//given an attribute which is x-y, return the expr
	Expr ICE::minusAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name)
	{
		typedef boost::tokenizer< boost::char_separator<char>> t_tokenizer;
		boost::char_separator<char> sep("-");
		t_tokenizer tok(attr_name, sep);
		std::string left_name = *(tok.begin());
		std::string right_name = *(++tok.begin());
		Expr left_expr, right_expr;
		for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it) {
			std::ostringstream oss; oss << *(it->first);
			if(oss.str() == left_name) left_expr = it->second;
			if(oss.str() == right_name) right_expr = it->second;
		}
		if (Bounded) {
			if(!bind::isBvConst(left_expr) || !bind::isBvConst(right_expr)) 
				LOGLINE("ice", errs() << "OPERAND TYPE WRONG (not bv)!\n");
			left_expr = mk<BV2INT>(left_expr);
			right_expr = mk<BV2INT>(right_expr);
		} else {
			if(!bind::isIntConst(left_expr) || !bind::isIntConst(right_expr))
				LOGLINE("ice", errs() << "OPERAND TYPE WRONG! (not int)\n");
		}
		int cut = sub_pt.get<int>("cut");
		Expr threshold = mkTerm<mpz_class>(cut, left_expr->efac());
		// Expr c1 = mkTerm<mpz_class>(1, left_expr->efac());
		// Expr c2 = mkTerm<mpz_class>(-1, left_expr->efac());
		// Expr decision_expr = mk<LEQ>(mk<PLUS>(mk<MULT>(c1, left_expr), mk<MULT>(c2, right_expr)), threshold);
		Expr decision_expr = mk<LEQ>(mk<MINUS>(left_expr, right_expr), threshold);

		return decision_expr;
	}

	//given an attribute which is x%y, return the expr
	Expr ICE::modAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name)
	{
		typedef boost::tokenizer< boost::char_separator<char>> t_tokenizer;
		boost::char_separator<char> sep("mod");
		t_tokenizer tok(attr_name, sep);
		std::string left_name = *(tok.begin());
		std::string right_name = *(++tok.begin());
		Expr left_expr = NULL, right_expr = NULL;
		for(ExprMap::iterator it = m_attr_name_to_expr_map.begin(); it!= m_attr_name_to_expr_map.end(); ++it) {
			std::ostringstream oss; oss << *(it->first);
			if(oss.str() == left_name) left_expr = it->second;
			if(oss.str() == right_name) right_expr = it->second;
		}

		if (right_expr == NULL) {
			bool right_has_only_digits = (right_name.find_first_not_of( "0123456789" ) == -1);
			if (right_has_only_digits && bind::isIntConst(left_expr)) { right_expr = mkTerm<mpz_class>(atoi(right_name.c_str()), left_expr->efac()); } 
			else { LOG("ice", errs() << "OPERAND TYPE WRONG!\n"); }
		} else if ( Bounded && !bind::isBvConst(right_expr) ) {
			LOG("ice", errs() << "OPERAND TYPE WRONG (not bv)!\n");
		} else if ( !Bounded && !bind::isIntConst(right_expr) ) {
			LOG("ice", errs() << "OPERAND TYPE WRONG! (not int)\n");
		}
		// if(!bind::isIntConst(left_expr)) { LOG("ice", errs() << "OPERAND TYPE WRONG!\n"); }
		if (Bounded) {
			if(!bind::isBvConst(right_expr)) 
				LOGLINE("ice", errs() << "OPERAND TYPE WRONG (not bv)!\n");
			left_expr = mk<BV2INT>(left_expr);
		} else {
			if(!bind::isIntConst(right_expr))
				LOGLINE("ice", errs() << "OPERAND TYPE WRONG! (not int)\n");
		}

		int cut = sub_pt.get<int>("cut");
		Expr threshold = mkTerm<mpz_class>(cut, left_expr->efac());
		Expr decision_expr = mk<LEQ>(mk<MOD>(left_expr, right_expr), threshold);

		return decision_expr;
	}


	// Collect unknowns in the rules
	void ICE::extractUnknowns(HornClauseDB &db) {
		LOGLINE("ice", errs() << ">>> Unknown search starts.\n");
		ExprVector all_preds; // can have duplicates!
		for(auto it = m_rules.begin(); it != m_rules.end(); ++it) {
			HornRule r = *it;
			all_preds.push_back(r.head());
			get_all_pred_apps(r.body(), db, std::back_inserter(all_preds));
		}

		for (Expr pred: all_preds) {
			Expr rel = bind::fname(pred);
			int size = bind::domainSz(rel);

			if (unknowns.find(rel) == unknowns.end()) {
				// rel has not been searched
				// initialize:  unknowns[rel] = <true, true, ..., true>
				// true means "KNOWN!" for now
				std::vector<bool> flags(size);
				for (int i = 0; i < size; i++)
					flags[i] = true;
				unknowns[rel] = flags;
			}

			for(int i=0; i<size; i++) {
				Expr name = pred->arg(i+1);
				std::ostringstream oss; oss << name;
				if (oss.str().find("@unknown") != -1 || oss.str().find ("_nondet_") != -1) {
					// name has "unknown" or "nondet"
					unknowns[rel][i] = false;
				}
			}
		}

		for(std::map<Expr, std::vector<bool>>::iterator itr = unknowns.begin(); itr != unknowns.end(); ++itr) {
			int knowns_count = 0;
			for (int i = 0; i < itr->second.size(); i++) {
				itr->second[i] = !itr->second[i];
				if (itr->second[i] == false)
					knowns_count++;
			}
			m_pred_knowns_count[itr->first] = knowns_count;
		}

		LOGLINE("ice", errs() << " -> Unknowns: \n");
		for(std::map<Expr, std::vector<bool>>::iterator itr = unknowns.begin(); itr != unknowns.end(); ++itr) {
			LOGIT("ice", errs() << blue << " " << *itr->first << ": " << normal << "<");
			for (int i = 0; i < itr->second.size(); i++) {
				LOGIT("ice", errs() << itr->second[i] << ", ");
			}
			LOGIT("ice", errs() << "> HAS NOT-UNKNOWNS: " << m_pred_knowns_count[itr->first] << "\n");
		}
		LOGLINE("ice", errs() << "<<< Unknown search done.\n");
	}

	// Collect integers in the rules ...
	// Fixme. It seems we only need to consider mod operations.
	void ICE::extractConstants(HornClauseDB &db) {
		struct IsREM : public std::unary_function<Expr, bool>
		{
			IsREM () {}
			bool operator() (Expr e) {return isOpX<REM>(e);}
		};

		for(auto it = m_rules.begin(); it != m_rules.end(); ++it)
		{
			HornRule r = *it;
			ExprVector body_pred_apps;

			filter (r.body(), IsREM(), std::back_inserter(body_pred_apps));

			for (Expr p : body_pred_apps) {
				Expr mod = p->right();
				std::ostringstream oss; oss << mod;
				bool right_has_only_digits = (oss.str().find_first_not_of( "0123456789" ) == -1);
				if (right_has_only_digits) {
					int cons = atoi(oss.str().c_str());
					if (cons > 0) ruleConstants.insert(cons);
					else if (cons < 0) ruleConstants.insert(-1*cons);
				}
			}
		}
	}


	// Substitute relations with their solution.
	// Enforce t is mapped to s if s is not null.
	Expr ICE::extractRelation(HornRule r, HornClauseDB &db, Expr t, Expr s)
	{
		Expr ruleBody = r.body();
		LOG("ice", errs() << cyan << "extract relation in target hornrule: " << blue << *ruleBody << "\n" << normal);
		ExprVector body_pred_apps;
		get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));
		// for (Expr p : body_pred_apps) LOG("ice", errs() << "filtered: " << *p << "\n");

		ExprMap body_map;
		for (Expr p : body_pred_apps) {
			if (p == t) {
				if (s == NULL) { body_map.insert(std::make_pair(p, mk<TRUE>(p->efac()))); }
				else { body_map.insert(std::make_pair(p, s)); }
			}
			else { body_map.insert (std::make_pair (p, m_candidate_model.getDef(p))); }
		}

		Expr body_constraints = replace(ruleBody, body_map);
		LOG("ice", errs() << cyan << " --> body constraint --> (extracted)  " << blue << *body_constraints << "\n" << normal);
		return body_constraints;
	}


	void ICE::genInitialCandidates (HornClauseDB &db)
	{
		// If predicate appears in Queries:
		//    predicate = False
		// Else
		//    predicate = True
		for(Expr rel : db.getRelations()) /* predicates */
		{
			Expr fapp = getFappFromRel(rel); /* predicate function */
			Expr True = mk<TRUE>(rel->efac());
			Expr False = mk<FALSE>(rel->efac());

			for (auto q : db.getQueries ()) {
				Expr query = q.get();
				if (bind::fname (query) == rel) { m_candidate_model.addDef(fapp, False); } /* predicate <- False */
				else { m_candidate_model.addDef(fapp, True); }  /* predicate <- True */
			}
		}

		LOGLINE("init candidate", errs() << "---- init candidate ---- (if (predicate in queries) then: False; else: True) \n");
		LOGIT("init candidate", errs() << cyan <<  m_candidate_model << normal);
		// LOGIT("init candidate", m_candidate_model.Print(errs()));
		LOGLINE("init candidate", errs() << "---- init candidate done ---- \n");

		// extractFacts (db, empty);
	}

	// For now always try to prove a query is false.
	void ICE::invalidateQueries (HornClauseDB &db)
	{
		// LOG("ice", errs() << mag << m_candidate_model << "\n" << normal);
		for(Expr rel : db.getRelations())
		{
			// errs() << "  - relation: " << *rel << "\n";
			Expr fapp = getFappFromRel(rel);
			Expr False = mk<FALSE>(rel->efac());

			for (auto q : db.getQueries ()) {
				Expr query = q.get();
				// errs() << "    | -- query " << *query << "\t";
				if (bind::fname (query) == rel) {
					// errs() << green << bold << "match\n" << normal;
					m_candidate_model.addDef(fapp, False);
					// errs() << " +++ add def " << blue << *fapp << " -> False" << normal << "\n";
				}
				else 
				{
					// errs() << red << "unmatch\n" << normal;
				}
			}
		}
		// errs() << bold << cyan << m_candidate_model << "\n" << normal;
	}

	// Match wheter an example corresponds to a fact.
	// Still not understand how this method should be used
	bool ICE::matchFacts (HornClauseDB &db, DataPoint p) {
		for(auto it = m_rules.begin(); it != m_rules.end(); ++it)
		{
			HornRule r = *it;
			// true -> head  &&  p is a model of head
			if (isOpX<TRUE>(r.body()) && isOpX<FAPP>(r.head()) && p.getPredName() == bind::fname(bind::fname(r.head()))) 
			{
				Expr head = r.head();
				Expr head_app = bind::fname(head);
				bool matched = true;
				LOGIT("ice", errs() << "[");
				for(int i=0; i<bind::domainSz(head_app); i++)
				{
					Expr arg_i_value = head->arg(i+1);
					LOGIT("ice", errs() << *arg_i_value);
					Expr arg_i_type = bind::domainTy(head_app, i);
					Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", head_app->efac ())), arg_i_type));

					if(isOpX<TRUE>(arg_i_value) || (isOpX<FALSE>(arg_i_value))) {
						std::list<Expr>::iterator it = p.getAttrValues().begin(); std::advance(it, i);
						// it -> p.attr_values[i]
						std::ostringstream oss; oss << **it;
						if(isOpX<TRUE>(arg_i_value)) { if(oss.str().compare("1") != 0) { matched = false; break; } }
						else if(isOpX<FALSE>(arg_i_value)) { if(oss.str().compare("0") != 0) { matched = false; break; } }
					}
					else if(bind::isBoolConst(arg_i_value)) { errs() << "  ::match bool const "; }
					else if(bind::isIntConst(arg_i_value)) { errs() << "  ::match int const "; }
					else if(bind::isBvConst(arg_i_value)) { errs() << "  ::match bv const "; }
					else { /* Other kind of constructs in fact rules not implemented yet ...*/
						errs() << bold << yellow << "Not Implemented yet.\n " << normal; 
						matched = false;
						break;
					}
				}
				LOGIT("ice", errs() << "]");

				if (matched) { 
					LOGLINE("ice", errs() << green << "* Matched! *\n" << normal); 
					return true; 
				}
			}
		}

		LOGLINE("ice", errs() << red << "* UnMatched! *\n" << normal);
		return false;
	}

	// Dealing with fact rules inside Horn System.
	// <1> Scan all the fact rules (true -> f (...)) <2>
	void ICE::reduceRules() {
		auto &db = m_hm.getHornClauseDB();
		ZSolver<EZ3> solver(m_hm.getZContext());
		m_fact_predicates.clear();
		m_rules.clear(); 

		for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it)
		{
			HornRule r = *it;
			// errs() << blue << "rule: " << HornRuleToStr(r, true) << normal;
			Expr head = r.head();
			Expr body = r.body();
			Expr rel = bind::fname(head);
			Expr fapp = getFappFromRel(rel); /* predicate function */
			Expr fmodel = mk<TRUE>(rel->efac());
			bool fact = false;
			if (isOpX<TRUE>(r.body()) && isOpX<FAPP>(r.head())) {
				ExprVector arg_list;
				ExprVector elements;
				int n_unknowns = 0;
				for(int i=0; i<bind::domainSz(rel); i++)
				{
					Expr arg_i_value = head->arg(i+1);
					Expr arg_i_type = bind::domainTy(rel, i);
					Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
					arg_list.push_back(arg_i);

					if(bind::isBoolConst(arg_i_value)) { n_unknowns++; LOG("ice", errs() << "bool const UNCERTAIN VALUE not Care: " << *arg_i_value << "\n"); }
					else if(bind::isIntConst(arg_i_value)) { n_unknowns++; LOG("ice", errs() << "int const UNCERTAIN VALUE not Care: " << *arg_i_value << "\n"); }
					else if(bind::isBvConst(arg_i_value)) { n_unknowns++; LOG("ice", errs() << "bv const UNCERTAIN VALUE not Care: " << *arg_i_value << "\n"); }
					else if(isOpX<TRUE>(arg_i_value)) { 
						fact = true; 
						elements.push_back(arg_i);
					} else if(isOpX<FALSE>(arg_i_value)) { 
						fact = true; 
						elements.push_back(mk<NEG>(arg_i));
					}
					else { /* Other kind of constructs in fact rules not implemented yet ...*/ }
				}
				if (n_unknowns == bind::domainSz(rel))
					fact = true;
				if (elements.size() >= 1)
					fmodel = mknary<AND>(elements.begin(), elements.end());
			}
			if (fact) { // Add fact rules into solutions.
				m_candidate_model.addDef(fapp, fmodel);
				m_fact_predicates.insert(bind::fname(rel));
			} else {
				m_rules.push_back(r);
			}
		}

		for (auto q : db.getQueries ()) {
			Expr query = q.get();
			Expr rel = bind::fname(query);
			m_fact_predicates.insert(bind::fname(rel));
			Expr fapp = getFappFromRel(rel); /* predicate function */
			Expr fmodel = mk<FALSE>(rel->efac());
			m_candidate_model.addDef(fapp, fmodel);
		}

		int i = 0;
		for(auto r: m_rules) {
			// LOGLINE("ice", errs() << " Check the rule: " << HornRuleToStr(r) << "\n");
			ExprVector all_pred_apps;
			all_pred_apps.push_back(r.head());
			get_all_pred_apps(r.body(), db, std::back_inserter(all_pred_apps));

			bool must_invalid = true;
			for (auto pred_app: all_pred_apps) {
				Expr rel = bind::fname(pred_app);
				if (std::find(m_fact_predicates.begin(), m_fact_predicates.end(), bind::fname(rel)) == m_fact_predicates.end()) {
					must_invalid = false;
					break;
				}
			}
			if (must_invalid) {
				if (checkHornRule(r, db, solver) != UNSAT) {
					errs() << bred << bold << "Bug! The following rule can go from (pass) Pre to (fail) Post directly." << normal << "\n";
					errs() << mag << bold << HornRuleToStr(r, true) << normal << "\n";
					exit(-1);
				}

				// LOGIT("ice", errs() << " Erase the rule (Pre=>xPost): " << HornRuleToStr(r, true) << "\n");
				m_rules.erase(m_rules.begin() + i);
			}
			i++;
		}

		// rebuild the rule
		// { int ruleno = 0; for (auto r: m_rules) { ruleIndex[r] = ruleno++; } }
		// errs() << "Candidate Model: \n" << m_candidate_model << "\n";
	}

	// Dealing with fact rules inside Horn System.
	// <1> Scan all the fact rules (true -> f (...)) <2>
	void ICE::extractFacts (HornClauseDB &db, ExprVector targets) {
		LOGIT("ice", errs() << "Extracting Fact Rules ...\n");
		LOGIT("ice", errs() << "NULL NOW...\n");
	}

	int ICE::countSamples (Expr pred, bool positive) {
		std::set<DataPoint>& data_set = m_neg_data_set; if (positive) { data_set = m_pos_data_set; }
		int count = 0;
		for (auto it = data_set.begin(); it != data_set.end(); ++it) {
			if (it->getPredName() == pred) { count++; }
		}
		return count;
	}

	void ICE::clearNegSamples (Expr app, bool b) { exit (-3); }

	Expr regulateAttrValue(Expr val) {
		//deal with uncertain values in cexs
		if(bind::isBoolConst(val))
		{
			LOG("ice", errs() << "UNCERTAIN VALUE: " << *val<< "\n");
			Expr uncertain_value = mk<FALSE>(val->efac());
			val = uncertain_value;
		}
		else if(bind::isIntConst(val))
		{
			LOG("ice", errs() << "UNCERTAIN VALUE: " << *val << "\n");
			Expr uncertain_value = mkTerm<mpz_class>(0, val->efac());
			val = uncertain_value;
		}
		else if(bind::isBvConst(val))
		{
			LOG("ice", errs() << "UNCERTAIN VALUE: " << *val << "\n");
			Expr uncertain_value = bv::bvnum (mpz_class ("0"), expr::op::bind::getWidth(val), val->efac());
			val = uncertain_value;
		}

		//convert true/false to 1/0 in C5 data point
		if(isOpX<TRUE>(val)) { val = mkTerm<mpz_class>(1, val->efac()); }
		else if(isOpX<FALSE>(val)) { val = mkTerm<mpz_class>(0, val->efac()); }

		return val;
	}

	std::list<Expr> modelToAttrValues(ZModel<EZ3> model, Expr pred)
	{
		std::list<Expr> attr_values;
		for(int i=0; i<bind::domainSz(bind::fname(pred)); i++)
		{
			Expr arg_i = pred->arg(i+1);
			Expr arg_i_value = model.eval(arg_i);
			arg_i_value = regulateAttrValue(arg_i_value);
			attr_values.push_back(arg_i_value);
		}
		return attr_values;
	}

	Expr getUnknownAttrValue(Expr val) {
		//deal with uncertain values in cexs
		if(bind::isBoolConst(val))
		{
			LOG("ice", errs() << "UNCERTAIN VALUE: " << *val<< "\n");
			Expr uncertain_value = mk<FALSE>(val->efac());
			val = uncertain_value;
		}
		else if(bind::isIntConst(val))
		{
			LOG("ice", errs() << "UNCERTAIN VALUE: " << *val << "\n");
			Expr uncertain_value = mkTerm<mpz_class>(0, val->efac());
			val = uncertain_value;
		}
		else if(bind::isBvConst(val))
		{
			LOG("ice", errs() << "UNCERTAIN VALUE: " << *val << "\n");
			Expr uncertain_value = bv::bvnum (mpz_class ("0"), expr::op::bind::getWidth(val), val->efac());
			val = uncertain_value;
		}

		//convert true/false to 1/0 in C5 data point
		if(isOpX<TRUE>(val)) { val = mkTerm<mpz_class>(1, val->efac()); }
		else if(isOpX<FALSE>(val)) { val = mkTerm<mpz_class>(0, val->efac()); }
		return val;
	}

	Expr constructExprFromTypeValueMap(std::pair<std::string, std::string> x, ExprFactory& efac) {
		using namespace expr::op;
		Expr typeE, valueE;
		std::string xtype = x.first;
		std::string xvalue = x.second;
		if (xtype == "Bool") {
			// std::cerr << "type: bool.\n";
			typeE = sort::boolTy(efac);
			if (xvalue == "true")
				valueE = mk<TRUE> (efac);
			else if (xvalue == "false")
				valueE = mk<FALSE> (efac);
			return valueE;
		}
		else if (xtype == "(_ BitVec 32)") {
			// std::cerr << "type: bv32. value: " << xvalue << "\n";
			int length = xvalue.length();
			// std::cerr << "1truncted: " << xvalue.substr(2, length-2) << ".\n";
			int xint = std::stoul(xvalue.substr(2, length-2), nullptr, 16);
			// std::cerr << "2converted: " << xint << ".\n";
			valueE = mkTerm (mpz_class (std::to_string(xint)), efac);
			// std::cerr << "3converted: " << xint << ".\n";
			typeE = bv::bvsort(32, efac);
			// return valueE;
		}
		else if (xtype == "Int") {
			// std::cerr << "type: int.\n";
			typeE = sort::intTy(efac);
			valueE = mkTerm (mpz_class (xvalue), efac);
			return valueE;
		}
		else if (xtype == "Real") {
			// std::cerr << "type: real.\n";
			typeE = sort::realTy(efac);
			valueE = mkTerm (mpq_class (xvalue), efac);
			return valueE;
		}
		else
			std::cerr << "error happens.\n";
		Expr outE = mk<BIND>(valueE, typeE);
		return outE;
	}

	std::list<Expr> modelToAttrValues(std::map<std::string, std::pair<std::string, std::string>> model, Expr pred) {
		std::list<Expr> attr_values;
		for(int i=0; i<bind::domainSz(bind::fname(pred)); i++)
		{
			Expr arg_i = pred->arg(i+1);
			std::string name = arg_i->to_string();
			Expr arg_i_value;
			if (model.count(name))
				arg_i_value = constructExprFromTypeValueMap(model[name], arg_i->efac());
			else
				arg_i_value = getUnknownAttrValue(arg_i);
			attr_values.push_back(arg_i_value);
		}
		return attr_values;
	}


	boost::tribool ICE::callExternalZ3ToSolve(ZSolver<EZ3> solver)
	{
		// outs() << "  " << bblue << "[Experimental] call external Z3 to solve constraint" << normal;
		LOGIT("ice", errs() << "  " << yellow << "Z3 solve ...... ");
		boost::tribool is_sat;
		std::ostringstream oss;
		solver.toSmtLib(oss);
		std::string smt2_to_solve = oss.str() + "\n(get-model)";
		// outs() << "SMT format for solving: " << gray << oss.str() << normal << "\n";
		// errs() << byellow << bold << "call external z3 to solve" << normal << "\n";
		std::ofstream smt_of(m_C5filename + ".smt2");
		smt_of << smt2_to_solve;
		smt_of.close();

		std::string command = Z3ExecPath + " " 
			+ m_C5filename + ".smt2" + " "
			+ "-T:10 "; // set timeout to 10s
		m_z3_model_str = "";

		LOG("ice", errs() << bgreen << "Call Z3 externally: " << command << normal << "\n");
		FILE* fp;
		if((fp = popen(command.c_str(), "r")) == NULL) { 
			LOG("ice", errs() << "popen error!\n"); 
			perror("popen failed!\n"); 
			is_sat = boost::indeterminate;
			return is_sat;
		}

		char buffer[1024];
		std::string model = "";
		while (fgets(buffer, 1024, fp) != NULL) {
			model += buffer;
		}
		// outs()  << red << model << normal << "\n";

		auto returnCode = pclose(fp);
		// if (returnCode == 0) { LOGLINE("ice", errs() << "RET 0 : SUCCESS\n"); } 
		// else { LOGLINE("ice", errs() << "RET " << returnCode << ": FAILURE\n"); }

		if (model.find("unsat") == -1) { // sat
			is_sat = true;
			int start = model.find("\n") + 1;
			m_z3_model_str = model.substr(start);
			LOGIT("ice", errs() << "SAT\n" << normal);
		} else {
			is_sat = false;
			LOGIT("ice", errs() << "UNSAT\n" << normal);
		}
		return is_sat;
	}

	bool ICE::parseModelFromString(std::string model_str) {
		std::replace(model_str.begin(), model_str.end(), '\n', ' ');
		std::replace(model_str.begin(), model_str.end(), '\t', ' ');
		m_z3_model.clear();
		int start = 0, next = 0, end = 0;
		next = model_str.find("(define-fun ", 0);
		// std::map<std::string, std::pair<std::string, std::string>> model;
		while (next != -1) {
			start = next;
			next = model_str.find("(define-fun ", start+1);
			if (next == -1)
				end = model_str.length() - 1;
			else
				end = model_str.rfind(")", next);
			// the current item is located as [start, end] "(define-fun " is 12 bit
			std::string item = model_str.substr(start, end+1-start);
			// outs()  << "---> [" << item << "]\n";
			int vname_start = 12;
			int vname_end = item.find(" ", vname_start);
			std::string vname = item.substr(vname_start, vname_end-vname_start);
			int vtype_start = item.find("() ", vname_end) + 3;
			int vtype_end = item.find(" ", vtype_start);
			if (item[vtype_start] == '(')
				vtype_end = item.find(")", vtype_start) + 1;
			std::string vtype = item.substr(vtype_start, vtype_end-vtype_start);
			int vval_start = item.find_first_not_of(" ", vtype_end);
			int vval_end = item.find(")", vval_start);
			std::string vval = item.substr(vval_start, vval_end-vval_start);
			if (vval[0] == '(') {
				// to handle the negative integer case
				vval = vval.substr(1, vval.length()-1);
				vval.erase(std::remove_if(vval.begin(), vval.end(), ::isspace), vval.end());
			}

			std::pair<std::string, std::string> type_value = {vtype, vval};
			// model[vname] = type_value;
			m_z3_model[vname] = type_value;
			// outs()  << bblue << "name: " << normal << vname << bblue << " type:" << normal << vtype << bblue << " val:" << normal << vval << "\n";
		}

		// outs()  << "<--- [return from parseModelFromString]\n";
		return true;
	}

	bool ICE::generatePositiveSamples (HornClauseDB &db, HornRule r, ZSolver<EZ3> solver, int& index, bool& run, ExprVector& changedPreds) {
		errs() << "########################## GENERATE POSITIVE SAMPLES ###########################\n";
		Expr r_head = r.head();
		if (bind::domainSz(bind::fname(r_head)) <= 0) { LOGLINE ("ice", errs () << "Rule cannot be refined.\n"); exit (-3); }

		// LOGLINE("ice", errs() << "1.2 SAT, RULE(head) need to be refined! NEED TO ADD More Examples\n");
		//get cex
		GetModel(solver);
		errs() << "HornRule: " << HornRuleToStr(r) << "\n";

		LOGLINE("ice", errs() << " solved model for r_body" << *r.body() << "\n"); 
		ExprVector body_pred_apps;
		get_all_pred_apps(r.body(), db, std::back_inserter(body_pred_apps));
		//print cex
		for (auto body_app : body_pred_apps) {
			std::list<Expr> attr_values = ModelToAttrValues(body_app);
			DataPoint neg_dp(bind::fname(bind::fname(body_app)), attr_values);
			LOGLINE("ice", errs() << "   |--" << *body_app << ": " << bgreen << DataPointToStr(neg_dp) << normal << "\n"); 
		}

		std::list<Expr> attr_values = ModelToAttrValues(r_head);
		DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
		LOGLINE("ice", errs() << " solved model for HEAD " << *r.head() << ": " << bgreen << DataPointToStr(pos_dp) << normal << "\n"); 

#if 0
		int orig_size = m_pos_data_set.size();
		addPosCex(pos_dp);
#endif

		// lijiaying added
		/*
		m_positive_trace = false;
		m_negative_trace = false;
		errs() << bold << bmag << "@@ RESET must be Positive trace **" << normal << "\n";
		errs() << bold << bmag << "@@ RESET must be Negative trace **" << normal << "\n";
		m_tmp_data_set.clear();
		m_tmp_data_set.insert(pos_dp);
		LOGLING("ice", errs() << "HORN RULE: " << HornRuleToStr(r) << "\n");
		*/
		m_tmp_data_set.insert(pos_dp);
		if (mustPositive(r)) {
			m_positive_trace = true;
			errs() << bold << bgreen << "@@ must be Positive trace (->positive_rule(sat))**" << normal << "\n";
		}
		if (mustNegative(r)) {
			m_negative_trace = true;
			errs() << bold << bblue << "@@ must be Negative trace (->negative_rule(sat))**" << normal << "\n";
		}

		run = sampleLinearHornCtrs(r_head, pos_dp, index, changedPreds);

		/*
		addImplChain(m_tmp_data_set, m_positive_trace, m_negative_trace);

		for (auto dp: m_tmp_data_set) {
			Expr pred = dp.getPredName();
			if (std::find(changedPreds.begin(), changedPreds.end(), pred) == changedPreds.end()) {
				LOGLINE("ice", errs() << "add " << *pred << " to changedPreds\n");
				changedPreds.push_back(pred);
			}
		}
		m_tmp_data_set.clear();
		*/
		// lijiaying end

#if 0	
		LOGLINE("ice", errs() << "head cex (point model, exclude unknowns): " << DataPointToStr(pos_dp, empty, false) << normal << "\n");
		if(m_pos_data_set.size() == orig_size + 1) //no duplicate
		{
			if (m_neg_data_set.size() > /*50*/ICESVMFreqPos) { 
				LOGLINE("ice", errs() << "SVM based Hyperplane Learning!\n"); 
				svmLearn (NULL); 
			}
			// LOGLINE("ice", errs() << red << "> Remove all the data for r_head " << *r_head << " in cex and neg_data_list\n" << normal);
			clearNegData(r_head);

			m_cex_list.push_back(pos_dp);
			addDataPointToIndex(pos_dp, index);
			LOGLINE("ice", errs() << "POS CEX, INDEX IS " << index << "\n");
			index++;

			run = sampleLinearHornCtrs(r_head, pos_dp, index, changedPreds);
			return run;
		}
		else // it is a duplicate data point
		{
			LOGLINE("ice", errs() << bred << "1.2 Duplicated positive points should be impossible." << normal << "\n");
			clearNegSamples (r_head, true);
			// exit (-3);
		}
#endif
		return true;
	}

	// Given a rule head, extract all rules using it in body, then add all such rules to the beginning of workList
	void addUsedToWorkList(HornClauseDB &db, std::vector<HornRule>& rules, std::list<HornRule> &workList, HornRule r)
	{
		for(auto it = rules.begin(); it != rules.end(); ++it)
		{
			if(*it == r) continue;
			HornRule rule = *it;
			Expr r_body = rule.body();
			ExprVector body_apps;
			get_all_pred_apps(r_body, db, std::back_inserter(body_apps));

			for (Expr body_app : body_apps) {
				if (bind::fname(body_app) == bind::fname(r.head())) {
					if(std::find(workList.begin(), workList.end(), *it) == workList.end()) { 
						workList.push_front(*it); 
					}
					break;
				}
			}
		}
	}

	// Given a rule, extract all rules using its body_apps in head, then add all such rules to the end of workList
	void addNewToWorkList (HornClauseDB &db, std::vector<HornRule>& rules, std::list<HornRule> &workList, HornRule r) {
		Expr r_body = r.body();
		ExprVector body_apps;
		get_all_pred_apps(r_body, db, std::back_inserter(body_apps));

		for(auto it = rules.begin(); it != rules.end(); ++it) {
			if(*it == r) continue;
			HornRule rule = *it;
			for (Expr body_app : body_apps) {
				if (bind::fname(body_app) == bind::fname(rule.head())) {
					if(std::find(workList.begin(), workList.end(), *it) == workList.end()) { workList.push_back(*it); }
					break;
				}
			}
		}
	}

	boost::tribool ICE::checkHornRule(HornRule& r, HornClauseDB& db, ZSolver<EZ3>& solver) 
	{
		solver.reset();
		Expr r_head = r.head();
		Expr r_head_cand = m_candidate_model.getDef(r_head);
		solver.assertExpr(mk<NEG>(r_head_cand));
		Expr body_formula = extractRelation(r, db, NULL, NULL);
		solver.assertExpr(body_formula);
		LOG("ice", errs() << "head candidate: " << blue << *r_head_cand << "\n" << normal);
		LOG("ice", errs() << "body candidate: " << blue << *body_formula << "\n" << normal);

		boost::tribool result = Solve(solver);
		return result;
	}

	void ICE::clearNegData(Expr& pred) {
		LOGLINE("ice", errs() << red << "> Remove all the data for " << *pred << " in cex and neg_data_list\n" << normal);
		m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(), 
					[pred,this](DataPoint p) { 
					return p.getPredName() == bind::fname(bind::fname(pred)) && m_neg_data_set.find(p) != m_neg_data_set.end();
					}), 
				m_cex_list.end());

		LOGLINE("ice", errs() << red << "  >Erase data from NEG_DATASET: " << normal);
		for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
			if (it->getPredName() == bind::fname(bind::fname(pred))) {
				LOGIT("ice", errs() << DataPointToStr(*it));
				m_neg_data_set.erase (it++); 
			} else { ++it; } 
		}
		LOGIT("ice", errs() << "\n");
		// Test Feature!!
		// lijiaying
		/*
			 m_neg_data_count.erase (pred);
			 for (std::set<DataPoint>::iterator it = m_must_neg_data_set.begin(); it != m_must_neg_data_set.end(); ++it) {
			 if (it->getPredName() == bind::fname(bind::fname(pred))) {
			 LOGIT("ice", errs() << DataPointToStr(*it));
			 addNegCex(*it);
			 } 
			 }
			 */
		// end lijiaying
	}

	void ICE::preparePosNegPredSet(HornClauseDB &db) {
		m_neg_pred_set.clear();
		m_pos_pred_set.clear();
		for (auto q: db.getQueries())
			m_neg_pred_set.insert(bind::fname(bind::fname(q)));

		for (auto r: db.getRules()) {
			if (isOpX<TRUE>(r.body()))
				m_pos_pred_set.insert(bind::fname(bind::fname(r.head())));
		}

		m_must_pos_rule_set.clear();
		m_must_neg_rule_set.clear();
		for (auto r: db.getRules()) {
			// errs() << blue << "rule: " << HornRuleToStr(r, true) << normal << "---------\n";
			Expr r_head_name = bind::fname(bind::fname(r.head()));
			bool must_neg = (m_neg_pred_set.count(r_head_name) > 0);

			ExprVector body_pred_apps;
			get_all_pred_apps(r.body(), db, std::back_inserter(body_pred_apps));
			bool must_pos = true;
			for (auto pred: body_pred_apps) {
				Expr pred_name = bind::fname(bind::fname(pred));
				// errs() << "    |---- " << *pred_name << "\n"; 
				must_pos = (m_pos_pred_set.count(pred_name) > 0)? must_pos : false;
			}

			if (must_pos) m_must_pos_rule_set.insert(r);
			if (must_neg) m_must_neg_rule_set.insert(r);
			// errs() << "  -- mustPositive: " << must_pos << "  mustNegative: " << must_neg << "\n";
		}

		// errs() << " MUST POSITIVE RULES: "; for(auto r : m_must_pos_rule_set) errs() << " " << HornRuleToStr(r); errs() << "\n";
		// errs() << " MUST NEGATIVE RULES: "; for(auto r : m_must_neg_rule_set) errs() << " " << HornRuleToStr(r); errs() << "\n";

	}


	static int solveConstraintTime = 0;
	bool ICE::solveConstraints(HornClauseDB &db, bool &isChanged, int &index)
	{
		solveConstraintTime++;
		std::list<HornRule> workList;
		workList.insert(workList.end(), m_rules.begin(), m_rules.end());
		workList.reverse();

		LOGIT("ice", errs() << green << bold << "=========================== Constraint Solving of Horn Clauses ============================\n" << normal);
		ZSolver<EZ3> solver(m_hm.getZContext());
		boost::tribool result;

		int loopi = 0;
		while (!workList.empty())
		{
			errs() << DataSetToStr() << "\n";
			errs() << CandidateToStr() << "\n";
			errs() << "\n\n\n";
			HornRule r = workList.front();
			workList.pop_front();
			// errs() << "----------------------------------------------------------------------------------------------------------------------\n";
			errs() << "*************************************************************************************************************************\n";
			bool updated = false; int counter = 0; bool posUpdated = false;

			LOGIT ("ice", errs() << bgreen << "Solve Constraint #" << solveConstraintTime << " --- loop #" << ++loopi << " times ---");
			errs() << normal << mag << " WorkList: " << normal; 
			errs() << underline << bold << blue << "(" << HornRuleToStr(r) << ")" << normal << bold << mag;
			for (auto rr : workList) 
				errs() << HornRuleToStr(rr); 
			errs() << normal << "\n";
			// LOGIT("ice", errs() << bold << green << "VERIFY Horn Rule: " << normal << mag << bold << HornRuleToStr(r) << normal << "\n" );

			Expr r_head = r.head();
			Expr r_body = r.body();
			ExprVector body_pred_apps;
			get_all_pred_apps(r_body, db, std::back_inserter(body_pred_apps));

			if (checkHornRule(r, db, solver) == UNSAT) 
				continue;
			ExprVector changedPreds;
			LOGLINE("ice", errs() << "add " << *bind::fname(bind::fname(r_head)) << " to changedPreds\n");
			changedPreds.push_back(bind::fname(bind::fname(r_head)));
			// changedPreds.push_back(bind::fname(*db.getRelations().begin()));
			
			m_positive_trace = false;
			m_negative_trace = false;
			m_tmp_data_set.clear();
			errs() << bold << bmag << "@@ RESET must be Positive trace **" << normal << "\n";
			errs() << bold << bmag << "@@ RESET must be Negative trace **" << normal << "\n";

			std::set<DataPoint> Neg_dps;
			for (auto body_app : body_pred_apps) {
				std::list<Expr> attr_values = ModelToAttrValues(body_app);
				DataPoint neg_dp(bind::fname(bind::fname(body_app)), attr_values);
				Neg_dps.insert(neg_dp);
				// m_tmp_data_set.insert(neg_dp);
				errs() << " |-> " << DataPointToStr(neg_dp, empty, false) << "\n";
			}

			if (bind::domainSz(bind::fname(r_head)) <= 0) {
				++counter;
				m_tmp_data_set.clear();
				m_tmp_data_set.insert(Neg_dps.begin(), Neg_dps.end());
				if (mustPositive(r)) {
					m_positive_trace = true;
					errs() << bold << bgreen << "@@ must be Positive trace (->positive_rule(sat))**" << normal << "\n";
				}
				if (mustNegative(r)) {
					m_negative_trace = true;
					errs() << bold << bblue << "@@ must be Negative trace (->negative_rule(sat))**" << normal << "\n";
				}
				errs() << " Head does not contain any parameters, thus can not refine!\n";
				addImplChain(m_tmp_data_set, m_positive_trace, m_negative_trace);
				m_tmp_data_set.clear();
				changedPreds.push_back(bind::fname(bind::fname(bind::fname(r_body))));
				LOGLINE("ice", errs() << "add " << *bind::fname(bind::fname(bind::fname(r_body))) << " to changedPreds\n");
				C5learn (changedPreds);
			} else {
				errs() << " Try to generate more samples!\n";
				do {
					++counter;
					m_tmp_data_set.clear();
					m_tmp_data_set.insert(Neg_dps.begin(), Neg_dps.end());
					bool run = true;
					updated = generatePositiveSamples (db, r, solver, index, run, changedPreds);
					if (!run) /* this rule is fine */ return false;

					addImplChain(m_tmp_data_set, m_positive_trace, m_negative_trace);
					for (auto dp: m_tmp_data_set) {
						Expr pred = dp.getPredName();
						if (std::find(changedPreds.begin(), changedPreds.end(), pred) == changedPreds.end()) {
							LOGLINE("ice", errs() << "add " << *pred << " to changedPreds\n");
							changedPreds.push_back(pred);
						}
					}
					if (updated)
						changedPreds.push_back(bind::fname(bind::fname(bind::fname(r_body))));
						LOGLINE("ice", errs() << "add " << *bind::fname(bind::fname(bind::fname(r_body))) << " to changedPreds\n");
						// changedPreds.push_back(r_body);
					C5learn (changedPreds);
				} while(updated);
			}
			// --- Extend worklist as we just go through a strengthening loop ----
			if (counter > 1) {
				if (posUpdated) addUsedToWorkList (db, m_rules, workList, r);
				else addNewToWorkList (db, m_rules, workList, r);
			}

			/*
			bool cleanBody = true;
			if (body_pred_apps.size() > 0) {
				for (Expr body_app : body_pred_apps) {
					if (bind::domainSz(bind::fname(body_app)) > 0) {
						cleanBody = false; 
						break;
					}
				}
			}
			*/

			
#if 0
			if (cleanBody) {
				/////////////////////////////////////////////////////////////////////////////////////////////////////////
				//////////////////////////  BODY IS CLEAN (Simple Case)  ////////////////////////////////////////////////
				/////////////////////////////////////////////////////////////////////////////////////////////////////////
				// LOGIT("ice", errs() << bred << "[1] BODY is clean" << normal << "\n");
				if (bind::domainSz(bind::fname(r_head)) <= 0) 
				{
					errs() << bold << bmag << " >>>>>>>>>>>>>>>>>>>>>>> BODY, HEAD ARE CLEAN (CHECK DIRECTLY) >>>>>>>>>>>>>>>>>>>>>>>" << normal << "\n";
					/////////////////////////////////////////////////////////////////////////////////////////////////////////
					//////////////////////////  BODY, HEAD ARE CLEAN (CHECK DIRECTLY)  //////////////////////////////////////
					/////////////////////////////////////////////////////////////////////////////////////////////////////////
					// LOGIT("ice", errs() << red << " HEAD clean, Body clean. CHECK IT. Nothing is need to be refined!" << normal << "\n");
					// LOGLINE ("ice", errs() << "Verify a rule without unknown invariants.\n");
					if (checkHornRule(r, db, solver) == UNSAT) 
						continue;
					outs() << red << "1.1 Program is buggy.\n" << normal;
					std::list<Expr> attr_values;
					DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
					addPosCex(pos_dp);
					if (mustPositive(r)) addMustPosCex(pos_dp);
					if (mustNegative(r)) addMustNegCex(pos_dp);
					LOGLINE("ice", errs() << red << "Failed DataPoint: " << DataPointToStr(pos_dp, empty, false) << normal << "\n");
					failurePoint = m_pos_list.size()-1;
					return false;
				} 
				else 
				{
					errs() << bmag << bold << " >>>>>>>>>>>>>>>>>>>>>>>> BODY IS CLEAN, HEAD DIRTY (Generate More Samples) >>>>>>>>>>>>>>>>>> " << normal << "\n";
					/////////////////////////////////////////////////////////////////////////////////////////////////////////
					//////////////////////////  BODY IS CLEAN (Generate More Samples)  //////////////////////////////////////
					/////////////////////////////////////////////////////////////////////////////////////////////////////////
					// LOGIT("ice", errs() << bred << " [1].2 Head is not clean. Possibly need to be refined!" << normal << "\n");
					// Head is possibly need to be refined!
					// LOGLINE ("ice", errs() << bcyan << ">> Generate Initial Program States. RuleNo." << HornRuleToStr(r) << normal << "\n");
					do {
						if (checkHornRule(r, db, solver) == UNSAT) { 
							updated = false; 
							break; 
						}

						// Which predicates will be changed in this iteration of solving.
						ExprVector changedPreds;
						changedPreds.push_back(bind::fname(bind::fname(r_head)));
						changedPreds.push_back(bind::fname(*db.getRelations().begin()));

						bool run = true;
						updated = generatePositiveSamples (db, r, solver, index, run, changedPreds);
						// errs() << "[debug] run = " << run << "\n[debug] updated = " << updated << "\n";
						if (!run) /* this rule is fine */ 
							return false;
						if (updated) {
							isChanged = true; 
							posUpdated = true;
							/* for (auto pred: db.getRelations()) { 
							 * 	 Expr e = bind::fname(pred); changedPreds.push_back(e);
							 *   LOGLINE("ice", errs() << red << "1.2.1 add to changed Pred: " << *e << "\n" << normal);
							 * } 
							 */
							C5learn (changedPreds);
						}
						errs() << "\n";
					} while (updated);
					LOGLINE ("ice", errs() << bcyan << "1.2 << Generate Initial Program State Samples." << normal << "\n");
					// --- Extend work list as we just go through a strengthening loop ----
					addUsedToWorkList (db, m_rules, workList, r);
				}
			} 
			else 
			{
				errs() << bold << bmag << " >>>>>>>>>>>>>>>>>> BODY IS DIRTY >>>>>>>>>>>>>>>>>>>>>>>>" << normal << "\n";
				/////////////////////////////////////////////////////////////////////////////////////////////////////////
				///////////////////////////   BODY IS DIRTY (IMPLICATION)  //////////////////////////////////////////////
				/////////////////////////////////////////////////////////////////////////////////////////////////////////
				// LOGIT("ice", errs() << bred << " [2] BODY IS DIRTY. Might Both Head and Body need to be refined!" << normal << "\n");
				do {
					++counter;
					// errs() << normal << mag << " WorkList: " << bold; 
					errs() << bold << green << "Verification Round " << counter << " " << normal;
					errs() << bold << blue << underline << "(" << HornRuleToStr(r) << ")" << normal << bold << mag;
					for (auto rr : workList) 
						errs() << HornRuleToStr(rr); 
					errs() << normal << "\n";
					// LOGLINE("ice", errs() << bold << green << "Rule Verification Round " << counter << mag << HornRuleToStr(r) << normal << "\n");
					result = checkHornRule(r, db, solver);

					// Which predicates will be changed in this iteration of solving.
					ExprVector changedPreds;
					// FixMe. Bad Code.
					// changedPreds.push_back (bind::fname(*(db.getRelations().begin())));
					Expr e = bind::fname(*(db.getRelations().begin()));
					changedPreds.push_back(e);
					updated = false;

					if(result != UNSAT) 
					{
						GetModel(solver);
						LOG("ice", errs() << "SAT, NEED TO ADD More Examples\n");
						updated = true; isChanged = true;
						std::set<DataPoint> negPoints;

						//print cex
						errs() << cyan << "get candidate for each body_predicate that has parameters: " << normal << "\n";
						for (Expr body_app : body_pred_apps) {
							errs() << gray << *body_app << normal;
							// No counterexample can be obtained from it because it is clean.
							assert (bind::domainSz(bind::fname(body_app)) > 0); 
							// if (bind::domainSz(bind::fname(body_app)) <= 0) // No counterexample can be obtained from it because it is clean.
							// { errs() << " xxx \n"; continue; }

							std::list<Expr> attr_values = ModelToAttrValues(body_app);
							// Presumbaly add counterexample
							DataPoint neg_dp(bind::fname(bind::fname(body_app)), attr_values);
							negPoints.insert(neg_dp);
							errs() << " |-> " << DataPointToStr(neg_dp, empty, false) << "\n";
						}


						// If the counterexample is already labeled positive;
						// Add its successive (aka. state transition) to positives instead.
						bool foundPos = true;
						for (DataPoint neg_dp : negPoints) {
							if (DebugLevel>3) errs() << " search datapoint: " << red << DataPointToStr(neg_dp) << normal << " in m_pos_data_set: ";
							if (m_pos_data_set.find(neg_dp) != m_pos_data_set.end()) { 
								if (DebugLevel>3) errs() << bold << green << " Found " << normal << "\n"; 
							}
							else { 
								foundPos = false; 
								if (DebugLevel>3) errs() << bold << red << " not Found " << normal << "\n"; 
								break; 
							}
						}

						if (foundPos) /* the whole negPoints */
						{
							errs() << bold << bmag << "      >>>>>>>>>>>>>>>>>>>> BODY IS DIRTY (Positive => Positive) >>>>>>>>>>>>>>>>>>" << normal << "\n";
							/////////////////////////////////////////////////////////////////////////////////////////////////////////
							///////////////////////////   BODY IS DIRTY (Positive => Positive)  /////////////////////////////////////
							/////////////////////////////////////////////////////////////////////////////////////////////////////////
							errs() << red << " [2.yPos] body instance is in Pos, Refine the Head!" << normal << "\n";
							// LOGLINE("diff", errs() << red << "[IMPLICATION]!! Body=/=>Head, and body model is found in POSitive, so refine Head!! \n" << normal);
							// if the body datapoint found in Positive, then head must be refined!

							std::list<Expr> attr_values = ModelToAttrValues(r_head);
							DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
							errs() << " get HEAD cex (positive): " << mag << DataPointToStr(pos_dp) << normal << "\n";
							if (mustPositive(r)) addMustPosCex(pos_dp);
							if (mustNegative(r)) addMustNegCex(pos_dp);
							int orig_size = m_pos_data_set.size();
							addPosCex(pos_dp);

							if (bind::domainSz(bind::fname(r_head)) <= 0) 
							{
								// Positive ==> HEAD with no params
								LOGLINE("diff", errs() << bred << " Positive ==> Head with no params!! (ERROR)" << normal << "\n");
								outs()<<" [2].1 Program is buggy. " << bred << "[lijiaying Question: the Point might be put in Pos wrongly]" << normal << "\n";
								LOGLINE("ice", errs() << red << "Collect the buggy implication (body_model -> head_model(empty)).\n" << normal);
								failurePoint = m_pos_list.size()-1;
								std::list<int> preIndices; for (DataPoint neg_dp : negPoints) { preIndices.push_back(m_pos_index_map[neg_dp]); } postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));
								return false;
							}

							// should be Positive => Positive !
							// LOGLINE("diff", errs() << bred << " Positive ==> Positive !! " << normal << "\n");
							if(m_pos_data_set.size() == orig_size + 1) //no duplicate
							{
								// ---- Doubly check if the below code is necessary
								clearNegData(r_head);

								// ---- Clean negative samples for body apps as well
								for (Expr body_app : body_pred_apps) { if (bind::domainSz(bind::fname(body_app)) <= 0) continue; clearNegData(body_app); }

								// LOGLINE("ice", errs() << "POS CEX, INDEX IS " << index << "\n");
								m_cex_list.push_back(pos_dp); addDataPointToIndex(pos_dp, index);
								index++;

								std::list<int> preIndices; for (DataPoint neg_dp : negPoints) { preIndices.push_back(m_pos_index_map[neg_dp]); } postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));
								posUpdated = true;

								bool run = sampleLinearHornCtrs(r_head, pos_dp, index, changedPreds);
								if (!run) return false;

								Expr e = pos_dp.getPredName(); // e is head
								if (std::find(changedPreds.begin(), changedPreds.end(), e) == changedPreds.end())
									changedPreds.push_back (e);
								LOGLINE("ice", errs() << red << " 3.1. add to changed Pred: " << *e << "\n" << normal);
							}
							else //it is a duplicate data point
							{
								LOGLINE("ice", errs() << bred << "[2].2 ERROR. Head should have classified correct on this sample] Duplicated positive points should be impossible.\n" << normal);
								LOGIT("ice", errs() << bred << " lijiaying: It might be possible the predicate has not updated Last Time. " << *pos_dp.getPredName() << normal);
								clearNegSamples (r_head, true);
								m_buggy = true;
								return false;
								//exit (-3);
							}
						} 
						else 
						{  // foundPos = False
							errs() << bold << bmag << "      >>>>>>>>>>>>>>>>>>>> BODY IS DIRTY (Pure Implication) >>>>>>>>>>>>>>>>>>> " << normal << "\n";
							/////////////////////////////////////////////////////////////////////////////////////////////////////////
							///////////////////////////   BODY IS DIRTY (Pure Implication)  /////////////////////////////////////////
							/////////////////////////////////////////////////////////////////////////////////////////////////////////
							// LOG("diff", errs() << "[2.xPos]!! " << bred << "PURE IMPLICATION" << normal << "\n");
							errs() << red << " [2.PureImplication] body instance is not in Pos!" << normal << "\n";
							for (DataPoint neg_dp : negPoints) {
								if (m_pos_data_set.find(neg_dp) != m_pos_data_set.end()) /* Found this in positive set. */ 
								{ 
									errs() << "  Found sample " << red << DataPointToStr(neg_dp, empty, false) << " in positive set. \n"; 
									LOGLINE("ice", errs() << red << "Inconsisitency: such as body1, body2 ==> head!  Only One of Body1/2 is stored.." << normal << "\n");
								} 
								else 
								{
									if (mustPositive(r)) addMustPosCex(neg_dp);
									if (mustNegative(r)) addMustNegCex(neg_dp);
									int org_size = m_neg_data_set.size();
									addNegCex(neg_dp);

									if(m_neg_data_set.size() == org_size + 1) //no duplicate
									{
										errs() << red << "  [2.xPos:PureImplication.xNeg] !" << normal << " add new neg sample: " << DataPointToStr(neg_dp) << "\n";
										// LOGLINE("ice", errs() << "NEG CEX, INDEX IS " << index << "\n");
										m_cex_list.push_back(neg_dp); addDataPointToIndex(neg_dp, index);
										index++;

										Expr e = neg_dp.getPredName(); // e is one of the bodies 
										if (std::find(changedPreds.begin(), changedPreds.end(), e) == changedPreds.end())
											changedPreds.push_back (e);
										LOGLINE("ice", errs() << green << "  insert new predicate to ChangedPred: " << *e << "\n" << normal);

										/*
											 if (changedPreds.size() <= 1 || std::find(changedPreds.begin(), changedPreds.end(), neg_dp.getPredName()) == changedPreds.end())
											 {
											 Expr e = neg_dp.getPredName();
											 changedPreds.push_back (e);
										// changedPreds.push_back(pos_dp.getPredName());
										LOGLINE("ice", errs() << green << "  insert new predicate to ChangedPred: " << *e << "\n" << normal);
										}
										*/

										/*
											 std::map<Expr, int>::iterator it = m_neg_data_count.find(neg_dp.getPredName());
											 if (it != m_neg_data_count.end() && it->second > ICESVMFreqNeg && it->second % ICESVMFreqNeg == 0) {
											 LOG("ice", errs() << "SVM based Hyperplane Learning!\n"); 
											 svmLearn (neg_dp.getPredName());
											 }
											 */
									}
									else //it is a duplicate data point
									{ 
										LOGLINE("ice", errs() << bred << "    [2.xPos:Pureimplication.yNeg] Duplication! body instance is already in NegSet. " << normal << "\n"); 
										LOGLINE("ice", errs() << bred << "    lijiaying: Not possible, because the sample is generated based on the rule, and the rule is based on the learned result!" << normal << "\n"); 
										LOGLINE("ice", errs() << bred << "      Unless the learned result is not updated! Pred: " << *neg_dp.getPredName() << normal << "\n"); 
										// outs() << gray; solver.toSmtLib(outs()); outs() << normal;
										errs() << "save the smt2 constraint into file.\n";
										std::ofstream of_smt2(m_C5filename + ".bug.smt2");
										solver.toSmtLib(of_smt2);
										of_smt2.close();
										// check Z3 correctness
										clearNegSamples (neg_dp.getPredName(), false); 
										m_buggy = true;
										return false;
									}
								}
							}
						}
					}

					if (updated) {
						// Ask machine learning for a new invariant for body_app.
						// Expr pre = m_candidate_model.getDef(body_app);
						C5learn (changedPreds);
					}
					errs() << "\n";
				} while (updated);

				// --- Extend worklist as we just go through a strengthening loop ----
				if (counter > 1) {
					if (posUpdated) addUsedToWorkList (db, m_rules, workList, r);
					else addNewToWorkList (db, m_rules, workList, r);
				}
			}
#endif
		}
		// LOGLINE("ice", errs() << "==================================================================\n");
		LOGIT("ice", errs() << red << "=========================== Constraint Solving of Horn Clauses ============================\n" << normal);
		return true;
	}


	// convert a datapoint into a program state (3, 4) ==>  x=3 /\ y=4
	Expr ICE::constructStateFromPredicateAndDataPoint(Expr pred, DataPoint p) {
		ExprVector equations;
		for(int i=0; i<=bind::domainSz(pred); i++)
		{
			Expr var = bind::domainTy(pred, i);
			std::list<Expr>::iterator it = p.getAttrValues().begin();
			std::advance(it, i);
			Expr value = *it;

			Expr arg_i_type = bind::domainTy(bind::fname (pred), i);
			std::ostringstream oss; oss << *arg_i_type;
			if (oss.str().compare("BOOL") == 0) {
				oss.str(""); oss.clear(); oss << *value;
				if (oss.str().compare("1") == 0) { value = mk<TRUE>(var->efac()); } 
				else if (oss.str().compare("0") == 0){ value = mk<FALSE>(var->efac()); } 
				else { exit (-3); }
			}

			LOG("ice", errs() << gray << *var << " = " << *value << "  ");
			equations.push_back(mk<EQ>(var, value));
		}

		Expr this_state;
		if(equations.size() > 1) { this_state = mknary<AND>(equations.begin(), equations.end()); }
		else { this_state = equations[0]; }
		return this_state;
	}


	// Sample Horn Constraint System.
	// Fixme. Not suitable for non-linear Horn Constraint System.
	bool ICE::sampleLinearHornCtrs (Expr head, DataPoint p, int &index, ExprVector& changedPreds) {
		errs () << " Sample State From " << red << "expr: " << *head << " datapoint: " << DataPointToStr(p) << " current index:" << index << "\n" << normal;
		Expr this_state = constructStateFromPredicateAndDataPoint(head, p); 
		LOGLINE("ice", errs() << gray << " This state: " << *this_state << normal << "\n");

		// Predicate -> ValueVector
		std::map<Expr, ExprVector> relationToPositiveStateMap;
		if(relationToPositiveStateMap.find(bind::fname(head)) == relationToPositiveStateMap.end()) {
			ExprVector states;
			states.push_back(this_state);
			relationToPositiveStateMap.insert(std::make_pair(bind::fname(head), states));
		} else {
			ExprVector &states = relationToPositiveStateMap.find(bind::fname(head))->second;
			states.push_back(this_state);
		}

		std::map<HornRule, int> transitionCount;
		bool run = getReachableStates(transitionCount, relationToPositiveStateMap, head, p, index);
		if (!run) return false;

		if (DebugLevel >= 3) {
			LOGLINE("ice", errs() << mag << bold << "====================== THE WHOLE STATE MAP ========================" << normal << "\n");
			int i = 0;
			for(std::map<Expr, ExprVector>::iterator itr = relationToPositiveStateMap.begin(); itr != relationToPositiveStateMap.end(); ++itr) {
				LOGIT("ice", errs() << blue << i << "> ");
				LOGIT("ice", errs() << *(itr->first) << bold << " |--> " << normal);
				LOGIT("ice", errs() << "(");
				for(ExprVector::iterator itr2 = itr->second.begin(); itr2 != itr->second.end(); ++itr2) {
					LOGIT("ice", errs() << *(*itr2) << ", ");
				}
				LOGIT("ice", errs() << ")\n" << normal);
				i++;
			}
		}
		return true;
	}


	// Sample Horn Constraint System.
	// Fixme. Not suitable for non-linear Horn Constraint System.
	bool ICE::getReachableStates(std::map<HornRule, int> &transitionCount, std::map<Expr, ExprVector> &relationToPositiveStateMap, Expr from_pred, DataPoint p, int &index)
	{
		errs() << bcyan << bold << "********** [INFERENCE] get Reachable States >>>>> " << normal; 
		errs() << " from Predicate:" << gray << *from_pred << normal << " DataPoint: " << bgreen << DataPointToStr(p) << normal << "\n";
		auto &db = m_hm.getHornClauseDB();
		int count = 0;
		for(HornClauseDB::RuleVector::iterator itr = m_rules.begin(); itr != m_rules.end(); ++itr)
		{
			HornRule r = *itr;
			std::map<HornRule, int>::iterator itc = transitionCount.find(r);
			if (itc != transitionCount.end() && itc->second >= RuleSampleLen /*101*/) {
				// Avoid infinitely unroll a rule!
				// Fixme. Set maximum unrolling number to be 101 or ...
				continue;
			}

			ExprVector body_preds;
			get_all_pred_apps(r.body(), db, std::back_inserter(body_preds));

			if(body_preds.size() == 1 && bind::fname(body_preds[0]) == bind::fname(from_pred)) // r.body == from  meaning  from->***
			{
				if (DebugLevel>3) errs() << green << " > found a rule to do the inference: RuleNo." << normal << blue << bold << HornRuleToStr(r) << normal << "\n";
				Expr this_state = constructStateFromPredicateAndDataPoint(body_preds[0], p); 
				LOGLINE("ice", errs() << gray << " This state: " << *this_state << normal << "\n");

				count++;
				bool run = getRuleHeadState(transitionCount, relationToPositiveStateMap, r, this_state, m_pos_index_map[p], index);
				if (!run) {
					if (DebugLevel>3) LOGLINE("ice", errs() << red << " < run == false. from Predicate:" << *from_pred << normal << "\n");
					return false;
				}
			}
		}
		errs() << green << " < finish the inference from Predicate=" << normal << *from_pred << "  Count=" << count << "\n\n";
		return true;
	}


	// Sample Horn Constraint System.
	// Fixme. Not suitable for non-linear Horn Constraint System.
	bool ICE::getRuleHeadState(std::map<HornRule, int> &transitionCount, std::map<Expr, ExprVector> &relationToPositiveStateMap, HornRule r, Expr from_pred_state, int pindex, int &index)
	{
		Expr r_head = r.head();
		// LOGIT("ice", errs() << "   " << "=>=>=>=>=>" << mag << " get RuleHeadSample " << bold << HornRuleToStr(r) << normal);
		// LOGIT("ice", errs() << " FromState:" << *from_pred_state << normal << "\n");
		// LOGIT("ice", errs() << " RULE HEAD: " << *(r.head()) << "\n");
		// LOGIT("ice", errs() << "RULE BODY: " << *(r.body()) << "\n");
		LOGIT("ice", errs() << " TRY to get an instance of RULE HEAD: " << *(r.head()) << "\n");
		auto &db = m_hm.getHornClauseDB();
		ZSolver<EZ3> solver(m_hm.getZContext());

		solver.assertExpr(from_pred_state);
		solver.assertExpr(extractTransitionRelation(r, db));
		//solver.toSmtLib(outs());
		boost::tribool isSat = Solve(solver);

		int iteri = 0;
		// while(isSat)
		while(isSat != UNSAT)
		{
			/*
			if (isSat == UNSAT) {
				if (mustNegative(r)) {
					m_positive_trace = true;
					errs() << bold << red << "@@ must be Positive trace (->negative_rule(unsat))**" << normal << "\n";
				}
				break;
			}
			*/
			if (mustPositive(r)) {
				m_positive_trace = true;
				errs() << bold << bgreen << "@@ must be Positive trace (->positive_rule(sat))**" << normal << "\n";
			}
			if (mustNegative(r)) {
				m_negative_trace = true;
				errs() << bold << bblue << "@@ must be Negative trace (->negative_rule(sat))**" << normal << "\n";
			}
			GetModel(solver);
			std::list<Expr> attr_values;
			if(bind::domainSz(bind::fname(r_head)) == 0) //Fixme. reach a predicate with empty signature.
			{
				outs() << red << "Reach a predicate with empty signature.\n" << normal; 
				if (mustNegative(r))
					outs() << blred << "  -->| encounter the postcondition, and sat, thus MUST negative.\n" << normal; 
				LOGLINE("ice", outs() << bred << bold << " Program is buggy. [lijiaying: not bug for now.]" << normal << "\n");
				DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
				addPosCex(pos_dp);
				failurePoint = m_pos_list.size()-1;
				std::list<int> preIndices;
				preIndices.push_back(pindex);
				postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));
				// return false;
				return true;
			}

			ExprVector equations;
			ExprVector abstractEquations; // Do not assgin concrete values to uncertainties.

			for(int i=0; i<=bind::domainSz(r_head); i++)
			{
				Expr var = bind::domainTy(r_head, i);
				bool isAbstract = false; // exist in the model
				Expr value;
#if !USE_EXTERNAL
				value = model.eval(var);
				{
					if(bind::isBoolConst(value)) { Expr uncertain_value = mk<FALSE>(value->efac()); value = uncertain_value; }
					else if(bind::isIntConst(value)) { Expr uncertain_value = mkTerm<mpz_class>(0, value->efac()); value = uncertain_value; } 
					else if(bind::isBvConst(value)) { Expr uncertain_value = bv::bvnum (mpz_class ("0"), expr::op::bind::getWidth(value), value->efac()); value = uncertain_value; }
					else { isAbstract = true; }
				}
#else
				std::string name = var->to_string();
				if (m_z3_model.count(name) > 0) {
					value = constructExprFromTypeValueMap(m_z3_model[name], var->efac());
					isAbstract = true;
				} else { /* uncertain value */ // arg_i_value = getUnknownAttrValue(arg_i);
					if(bind::isBoolConst(var)) { Expr uncertain_value = mk<FALSE>(var->efac()); value = uncertain_value; }
					else if(bind::isIntConst(var)) { Expr uncertain_value = mkTerm<mpz_class>(0, var->efac()); value = uncertain_value; } 
					else if(bind::isBvConst(var)) { Expr uncertain_value = bv::bvnum (mpz_class ("0"), expr::op::bind::getWidth(var), var->efac()); value = uncertain_value; }
				}
#endif
				// LOGIT("ice", errs() << gray << *var << " = " << *value << "  ");
				equations.push_back(mk<EQ>(var, value));
				if (isAbstract) 
					abstractEquations.push_back(mk<NEQ>(var, value));

				//convert true/false to 1/0 in C5 data point
				if(isOpX<TRUE>(value)) { value = mkTerm<mpz_class>(1, value->efac()); }
				if(isOpX<FALSE>(value)) { value = mkTerm<mpz_class>(0, value->efac()); }
				attr_values.push_back(value);
			}

			Expr this_state;
			if(equations.size() > 1) { this_state = mknary<AND>(equations.begin(), equations.end()); }
			else { this_state = equations[0]; }
			LOGLINE("ice", errs() << gray << " This head state: " << *this_state << normal << "\n");

			DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
			LOGLINE("ice", errs() << gray << " ---> head datapoint: " << DataPointToStr(pos_dp) << normal << "\n");
			m_tmp_data_set.insert(pos_dp);
			if (mustPositive(r)) {
				m_positive_trace = true;
				errs() << bold << bgreen << "@@ must be Positive trace (->positive_rule(sat))**" << normal << "\n";
			}
			if (mustNegative(r)) {
				m_negative_trace = true;
				errs() << bold << bblue << "@@ must be Negative trace (->negative_rule(sat))**" << normal << "\n";
			}

			// int orig_size = m_pos_data_set.size();
			// addPosCex(pos_dp);
			// if(m_pos_data_set.size() == orig_size + 1) //no duplicate
			{
				// LOG("ice", errs() << "POS CEX, INDEX IS " << index << "\n");
				// if (!ICEICE) { clearNegData(r_head); }
				m_cex_list.push_back(pos_dp);
				addDataPointToIndex(pos_dp, index);
				index++;

				std::list<int> preIndices;
				preIndices.push_back(pindex);
				postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));

				/* // lijiaying do not know why this part should be done
					 ExprVector arg_list;
					 Expr rel = bind::fname (r_head);
					 for(int i=0; i<bind::domainSz(rel); i++) {
					 Expr arg_i_type = bind::domainTy(rel, i);
					 Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
					 arg_list.push_back(arg_i);
					 }
					 Expr fapp = bind::fapp(rel, arg_list);
					 Expr True = mk<TRUE>(rel->efac());
					 m_candidate_model.addDef(fapp, True);
					 LOGLINE("ice", errs() << bold << red << "[not know] add def to model: " << *fapp << " -> " << *True << normal << "\n");
					 */

				if(relationToPositiveStateMap.find(bind::fname(r_head)) == relationToPositiveStateMap.end()) {
					ExprVector states;
					states.push_back(this_state);
					relationToPositiveStateMap.insert(std::make_pair(bind::fname(r_head), states));
				} else {
					ExprVector &states = relationToPositiveStateMap.find(bind::fname(r_head))->second;
					states.push_back(this_state);
				}

				std::map<HornRule, int>::iterator itc = transitionCount.find(r);
				if (itc == transitionCount.end()) { transitionCount.insert(std::make_pair(r, 1)); } 
				else { itc->second = itc->second + 1; }

				bool run = getReachableStates(transitionCount, relationToPositiveStateMap, r_head, pos_dp, index);
				if (!run) return false;

				itc = transitionCount.find(r);
				itc->second = itc->second - 1;
			}

			// Iterate with the next possible solution.
			iteri ++;
			// Enough samples ?
			if (iteri >= RuleSampleWidth) { break; }

			Expr notagain;
			if(abstractEquations.size() > 1) { notagain = mknary<OR>(abstractEquations.begin(), abstractEquations.end()); } 
			else if (abstractEquations.size() == 1) { notagain = abstractEquations[0]; } 
			else { break; }// There is nothing to be re-sampled ?

			solver.assertExpr(notagain);
			boost::tribool isSat = Solve(solver);
		}
		return true;
	}

	void countInvSize (Expr body_formula) {
		if (isOpX<OR> (body_formula)) {
			for (Expr arg : mk_it_range (body_formula->args_begin(), body_formula->args_end ())) {
				if (isOpX<AND> (arg)) { outs() << arg->arity() << ", "; }
				else { outs() << "1, "; }
			}
		} else {
			if (isOpX<AND> (body_formula)) { outs() << body_formula->arity() << ", "; } 
			else { outs() << "1, "; }
		}
		outs() << "\n";
	}

	// ICE: Induction CounterExample guided invariant inference.
	void ICE::runICE()
	{
		m_buggy = false;
		std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
		//load the Horn clause database
		auto &db = m_hm.getHornClauseDB ();
		db.buildIndexes ();
		LOG("ice", errs() << "DB: \n" << cyan << db << normal);
		errs() << yellow << bold;
		errs() << "=========================start runICE method==================================\n";
		errs() << "  DebugLevel=" << DebugLevel << "\n";
		errs() << "  Bounded=" << Bounded << "\n";
		errs() << "  ShowC5NameFile=" << ShowC5NameFile << "\n";
		errs() << "  ShowC5IntervalFile=" << ShowC5IntervalFile << "\n";
		errs() << "  ShowC5DataFile=" << ShowC5DataFile << "\n";
		errs() << "  ShowC5HexDataFile=" << ShowC5HexDataFile << "\n";
		errs() << "  ShowC5JsonFile=" << ShowC5JsonFile << "\n";
		errs() << "  ShowC5JsonStruct=" << ShowC5JsonStruct << "\n";
		errs() << "  ShowDataSet=" << ShowDataSet << "\n";
		errs() << normal;

		for (auto rel : db.getRelations())
			LOG("ice", errs() << "db relation: " << cyan << bold << *rel << normal << "\n");
		errs() << "===========================================================\n";

		// init the rule
		{ int ruleno = 0; for (auto r: db.getRules()) { ruleIndex[r] = ruleno++; } }

		std::ofstream ruleout("rule.txt");
		ruleout << "C5 NAME TO PRED NAME MAP\n";
		for(auto it = m_rel_to_c5_rel_name_map.begin(); it != m_rel_to_c5_rel_name_map.end(); ++it) 
			ruleout << *(it->second) << "    " << *(it->first) << "\n"; 
		ruleout << "\n\n";
		for (auto r: db.getRules()) {
			ruleout << HornRuleToStr(r, true) << "\n";
		}
		ruleout.close();

		preparePosNegPredSet(db);
		reduceRules();

		// LOGIT("ice", errs() << mag << "Rebuild m_must_pos_rule_set:\n" << normal);
		std::set<HornRule> tmp_rules;
		for (auto r: m_must_pos_rule_set) {
			if (std::find(m_rules.begin(), m_rules.end(), r) != m_rules.end()) {
				tmp_rules.insert(r);
			}
		}
		m_must_pos_rule_set.clear();
		for (auto rule : tmp_rules)
			m_must_pos_rule_set.insert(rule);
		tmp_rules.clear();
		// LOGIT("ice", errs() << mag << "Rebuild m_must_neg_rule_set:\n" << normal);
		for (auto r: m_must_neg_rule_set) {
			if (std::find(m_rules.begin(), m_rules.end(), r) != m_rules.end()) {
				tmp_rules.insert(r);
			}
		}
		m_must_neg_rule_set.clear();
		for (auto rule : tmp_rules)
			m_must_neg_rule_set.insert(rule);
		tmp_rules.clear();

		// rebuild the rule
		ruleIndex.clear();
		{ int ruleno = 0; 
			for (auto r: m_rules) { 
				ruleIndex[r] = ruleno++; 
			} 
		}

		//*/
		
		setupC5();

		LOGLINE("ice", errs() << "Extracted Fact Rules.\n");
		for (auto fact_pred: m_fact_predicates)
			errs() << "Fact Predicate: " << *fact_pred << "\n";
		LOGIT("ice", errs() << "=============================" << normal << "\n");
		LOGIT("ice", errs() << "Model Candidates: \n" << green << bold << m_candidate_model << normal);
		LOGIT("ice", errs() << "=============================" << normal << "\n");
		LOGIT("ice", errs() << mag << "Reduced Rules:\n");
		for (auto r : m_rules)
			LOGIT("ice", errs() << " ==> " << HornRuleToStr(r, true) << "\n");
		LOGIT("ice", errs() << "=============================" << normal << "\n");
		errs() << " MUST POSITIVE RULES: "; 
		for(auto r : m_must_pos_rule_set) errs() << " " << HornRuleToStr(r); 
		errs() << "\n=============================\n";
		errs() << " MUST NEGATIVE RULES: "; 
		for(auto r : m_must_neg_rule_set) errs() << " " << HornRuleToStr(r); 
		errs() << "\n=============================\n";

		// save the map from predicate name to C5-form predicate name
		// save the reduced rules
		std::ofstream ruleout2("rule-reduce.txt");
		ruleout2 << "C5 NAME TO PRED NAME MAP\n";
		for(auto it = m_rel_to_c5_rel_name_map.begin(); it != m_rel_to_c5_rel_name_map.end(); ++it) 
			ruleout2 << *(it->second) << "    " << *(it->first) << "\n"; 
		ruleout2 << "\n\n";
		for (auto r: m_rules) {
			ruleout2 << HornRuleToStr(r, true) << "\n";
		}
		ruleout2.close();

		// genInitialCandidates(db);

		int index = 0;
		bool isChanged = true;
		int c = 0;
		n_svm_calls = 0;
		failurePoint = -1;
		bool no_verification_found_error;
		
		while(isChanged) //There are still some counterexamples to find
		{
			isChanged = false;
			no_verification_found_error = solveConstraints(db, isChanged, index);
			if (!no_verification_found_error) { 
				errs() << DataSetToStr(true);
				break; /* A buggy program is catched. */ 
			}
			c ++;
		}

		std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
		outs() << "************** CHCs Solved in " << (std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count()) /1000000.0 << " (secs) **************\n\n";

		if (no_verification_found_error && !m_buggy) {
			outs() << "************** Program is correct **************\n";
			LOGIT("ice", errs() << "FINAL INVARIANTS MAP:\n");
			for(Expr rel : db.getRelations())
			{
				ExprVector arg_list;
				for(int i=0; i<bind::domainSz(rel); i++)
				{
					Expr arg_i_type = bind::domainTy(rel, i);
					Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("v", rel->efac ())), arg_i_type));
					arg_list.push_back(arg_i);
				}
				Expr fapp = bind::fapp(rel, arg_list);
				Expr cand = m_candidate_model.getDef(fapp);
				LOGIT("ice", errs() << "REL: " << *fapp << ", CAND: " << *cand << "\n");
				outs() << "REL: " << *fapp << " -- invariant size: ";
				countInvSize (cand);
			}
			outs() << "************** Program Correctness End **************\n\n";
		} else {
			outs() << "************** Program is buggy **************\n";
			outs() << "Buggy Trace:\n";
			drawPosTree ();
			outs() << "************** Buggy Trace End **************\n\n";
		}

		outs() <<"************** Learning Statistics **************:\n";
		outs() <<"Total CHC size: " << db.getRules().size() << "\n";
		outs() <<"Total Relation size: " << db.getRelations().size() << "\n";
		outs() <<"Total Var size: " << db.getVars().size() << "\n";
		outs() <<"Neg sample size: " << m_neg_data_set.size() << "\n";
		outs() <<"Pos sample size: " << m_pos_data_set.size() << "\n";
		outs() <<"Total sample size: " << m_neg_data_set.size() + m_pos_data_set.size() << "\n";
		outs() <<"Iteration number: " << index << "\n";
		outs() <<"************** Learning Statistics End **************\n\n";

		// Dump the invariants into file, for validation with Houdini
		if (!ICEInvDump.empty ()) { saveInvsToSmtLibFile(); }

		addInvCandsToProgramSolver();
	}
}
