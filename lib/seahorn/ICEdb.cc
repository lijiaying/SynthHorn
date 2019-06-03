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

#include "ufo/Stats.hh"
#include "color.hh"

using namespace llvm;


	

static llvm::cl::opt<std::string>
ICEInvDump("horn-ice-inv-dump", llvm::cl::desc("ICE Invariants Dump File:"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
C5ExecPath("horn-ice-c5-exec-path", llvm::cl::desc("C5 Executable File Path:"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<unsigned>
RuleSampleLen ("horn-rule-sample-length", cl::Hidden, cl::init (101));

static llvm::cl::opt<unsigned>
RuleSampleWidth("horn-rule-sample-width", cl::Hidden, cl::init (1));

static llvm::cl::opt<std::string>
SVMExecPath("horn-ice-svm-exec-path", llvm::cl::desc("SVM Executable File Path:"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<unsigned>
SVMCParameter("horn-ice-svm-c-paramter", cl::Hidden, cl::init (100000));

static llvm::cl::opt<unsigned>
SVMCoeffBound("horn-ice-svm-coeff-bound", cl::Hidden, cl::init (0));

static llvm::cl::opt<unsigned>
SVMAHyperplane("horn-ice-svm-a-hyperplane", cl::Hidden, cl::init (0));

static llvm::cl::opt<unsigned>
ICEMod("horn-ice-mod", cl::Hidden, cl::init (0));

static llvm::cl::opt<unsigned>
ICESVMFreqPos("horn-ice-svm-call-freq-pos", cl::Hidden, cl::init (50));

static llvm::cl::opt<unsigned>
ICESVMFreqNeg("horn-ice-svm-call-freq-neg", cl::Hidden, cl::init (100));

static llvm::cl::opt<unsigned>
LC("horn-ice-lc", cl::Hidden, cl::init (0));

static llvm::cl::opt<unsigned>
ICECatch("horn-ice-svm-caching", cl::Hidden, cl::init (0));

static llvm::cl::opt<unsigned>
ICELocalStrengthen("horn-ice-local-strengthening", cl::Hidden, cl::init(0));

static llvm::cl::opt<unsigned>
ICEOct("horn-ice-oct", cl::Hidden, cl::init(1));

static llvm::cl::opt<unsigned>
ICEICE("horn-ice-ice", cl::Hidden, cl::init(0));

namespace seahorn
{
  #define SAT_OR_INDETERMIN true
  #define UNSAT false

  /*ICEPass methods begin*/

  char ICEPass::ID = 0;

  bool ICEPass::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    LOG("ice-res", errs() << "Start ICE Pass\n";);
    Stats::resume ("ICE inv");
    ICE ice(hm);
    ice.setupC5();
    ice.genInitialCandidates(hm.getHornClauseDB());
    ice.runICE();
    LOG("ice-res", errs() << "RUN ICE SUCCESSCULLY\n";);
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

  void ICE::saveInvsToSmtLibFile()
  {
	  auto &db = m_hm.getHornClauseDB();
	  ZSolver<EZ3> solver(m_hm.getZContext());
	  errs() << "======================================================\n";
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::tag(bind::fname(rel), variant::variant(i, mkTerm<std::string> ("V", rel->efac ()))), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand_app = m_candidate_model.getDef(fapp);
		  LOG("ice", errs() << red << "HEAD: " << normal << *fapp << "\n";);
		  LOG("ice", errs() << red << "CAND: " << normal << *cand_app << "\n";);

		  solver.assertExpr(mk<IMPL>(fapp, cand_app));
	  }
	  errs() << "======================================================\n";
	  std::ofstream ofs(ICEInvDump.c_str());
	  solver.toSmtLib(errs());
	  solver.toSmtLib(ofs);
  }


  // Fixme. Helper function should be put into a util file
  std::vector<std::string> split_string(const std::string& str,
                                        const std::string& delimiter)
  {
      std::vector<std::string> strings;

      std::string::size_type pos = 0;
      std::string::size_type prev = 0;
      while ((pos = str.find(delimiter, prev)) != std::string::npos)
      {
				if (pos != prev)
          strings.push_back(str.substr(prev, pos - prev));
        prev = pos + 1;
      }

      // To get the last substring (or only, if delimiter is not found)
      strings.push_back(str.substr(prev));
      return strings;
  }

  void ICE::svmLearn (Expr targetName) { // (ExprVector targets) {
	  auto &db = m_hm.getHornClauseDB();

	  if (targetName == NULL && ICECatch == 0) {
		  m_svmattr_name_to_expr_map.clear ();
		  m_svmattr_name_to_str_map.clear ();
	  }

	  for (Expr rel : db.getRelations())
			LOG("ice", errs() << "db relation: " << cyan << bold << *rel << normal << "\n");

	  for (Expr rel : db.getRelations()) {
		  if (targetName != NULL && ICECatch == 0) {
			  if (targetName != bind::fname(rel)) continue;
			  else { // Remove previously found attributes.
				  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
				  std::stringstream ossA;
				  ossA << C5_rel_name;

				  ExprMap::iterator itr1 = m_svmattr_name_to_expr_map.begin();
				  while (itr1 != m_svmattr_name_to_expr_map.end()) {
					  std::stringstream ossB;
					  ossB << itr1->first;
				      if (ossB.str().find(ossA.str()) != -1) {
				         itr1 = m_svmattr_name_to_expr_map.erase(itr1);
				      } else {
				         ++itr1;
				      }
				  }
				  std::map<Expr, std::string>::iterator itr2 = m_svmattr_name_to_str_map.begin();
				  while (itr2 != m_svmattr_name_to_str_map.end()) {
					  std::stringstream ossB;
					  ossB << itr2->first;
					  if (ossB.str().find(ossA.str()) != -1) {
						 itr2 = m_svmattr_name_to_str_map.erase(itr2);
					  } else {
						 ++itr2;
					  }
				  }
			  }
		  }

		  // Excluse boolean variables for svm learning
		  std::vector<int> exclusives;
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  if (unknowns[rel][i]) { // Exclude unknowns from invariant inference.
				  exclusives.push_back(i);
			  	  continue;
			  }
			  Expr arg_i_type = bind::domainTy(rel, i);
			  std::ostringstream oss;
			  oss << arg_i_type;
			  if (oss.str().compare("BOOL") == 0) {
				  exclusives.push_back(i);
			  } else {
				  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
				  arg_list.push_back(arg_i);
			  }
		  }

		  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;

		  LOG("ice", errs() << "SVM DATA FILES ARE GENERATING\n";);
		  //generate .data file
		  std::ofstream data_of(m_C5filename + ".svm.data");
		  if(!data_of) return;

		  int pn = 0, nn = 0;
		  for(auto it = m_cex_list.begin(); it!=m_cex_list.end(); ++it) {
			  if (it->getPredName() == bind::fname(rel)) {
				  if(m_pos_data_set.count(*it) != 0) {
					  DataPoint pos_dp = *it;

					  data_of << "1";
					  pn ++;

					  int ind = 0;
					  for(Expr attr : pos_dp.getAttrValues()) {
						  // Not excluded as a boolean var.
						  if (exclusives.empty() || std::find(exclusives.begin(), exclusives.end(), ind) == exclusives.end()) { data_of << " " << *attr; }
						  ind ++;
					  }
					  data_of << "\n";
				  } else if(m_neg_data_set.count(*it) != 0) {
					  DataPoint neg_dp = *it;
					  data_of << "0";
					  nn ++;

					  int ind = 0;
					  for(Expr attr : neg_dp.getAttrValues()) {
						  if (exclusives.empty() || std::find(exclusives.begin(), exclusives.end(), ind) == exclusives.end()) { data_of << " " << *attr; }
						  ind ++;
					  }
					  data_of << "\n";
				  }
			  }
		  }
		  data_of.close();

		  // Call SVM to learn invariants
		  LOG("ice", errs() << "SVM DATA FILES ARE GENERATED\n";);

		  FILE *fp;
		  FILE *wp;
		  wp = fopen("SVM_temp","w+");
		  std::ostringstream oss;
		  oss << C5_rel_name;
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

		  std::string access = "r";
		  if((fp = popen(command.c_str(), access.c_str())) == NULL) { LOG("ice", errs() << "popen error!\n";); perror("popen failed!\n"); return; }
			LOG("ice", errs() << "call svm returns!\n";);

		  char buf[1024];
		  size_t status = fread(buf, sizeof(char), sizeof(buf), fp);
		  if(status == 0) { LOG("ice", errs() << "read from popen failed!\n";); return; }
		  fwrite(buf, 1, sizeof(buf), wp);
		  pclose(fp);
		  fclose(wp);

		  n_svm_calls ++;

		  std::ifstream if_svm(m_C5filename + ".attr");
		  std::ostringstream svm_buf;
		  char ch;
		  while(svm_buf && if_svm.get(ch))
		  { svm_buf.put(ch); }
		  if_svm.close();

		  std::string svm_string = svm_buf.str();
			LOG("ice", errs() << "svm: " << yellow << svm_string << normal << "\n";);
		  Expr zero = mkTerm<mpz_class>(0, rel->efac());
		  std::vector<std::string> lines = split_string (svm_string, "\n");
		  int ind = ICECatch == 0 ? 0 : m_svmattr_name_to_expr_map.size();  //0;
		  bool dt_learning = true;
		  for (auto itr = lines.begin(); itr != lines.end(); itr++) {
			  std::string line = *itr;
			  if (line.compare("true") != 0 && line.compare("false") != 0) {
				  ExprVector addargs;
				  std::ostringstream attross;
				  std::vector<std::string> thetas = split_string (line, " ");
					// c0 + c1 * x0 + c2 * x1 + ... + c{n+1} * xn >= 0
				  for (int i = 1; i < thetas.size(); i++) {
					  int coeff = atoi(thetas[i].c_str());
					  if (coeff == 0)
						  continue;

					  //if (coeff != 1 && coeff != -1) nonOctagon = true;
					  Expr c = mkTerm<mpz_class>(atoi(thetas[i].c_str()), rel->efac());
					  addargs.push_back (mk<MULT> (c, arg_list.at(i-1)));

					  attross << "(" << thetas[i].c_str() << "*" << C5_rel_name << "!" << arg_list.at(i-1) << ")+";
					  LOG("SVM", llvm::errs() << bold << red << "(" << thetas[i].c_str() << " * " << C5_rel_name << " ! " << arg_list.at(i-1) << ")+\n" << normal);
				  }

				  if (addargs.size () > 1 /*&& nonOctagon*/) {
					  Expr arg_i_type = sort::intTy(rel->efac());
					  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(ind, mkTerm<std::string> ("SVM", rel->efac ())), arg_i_type));
					  Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
					  m_svmattr_name_to_expr_map.insert(std::make_pair(attr_name_i, mknary<PLUS> (addargs)));
					  std::string strrep = attross.str();
					  m_svmattr_name_to_str_map.insert(std::make_pair(attr_name_i, strrep.substr(0, strrep.length() - 1)));
					  LOG("ice", errs() << bold << red << "SVM inferred a hyperlane: " << strrep.substr(0, strrep.length() - 1) << "\n" << normal);
				  }
			  }
			  ind++;
		  }
	  }
  }


  void ICE::setupC5() {
	  m_C5filename = "FromCmd";

	  //convert predicate names to the name format of C5
	  auto &db = m_hm.getHornClauseDB();
	  int rel_index = 0;
	  for(Expr rel : db.getRelations())
	  {
		  Expr C5_rel_name = variant::variant(rel_index, mkTerm<std::string>(std::string("PRED"), rel->efac()));
		  m_rel_to_c5_rel_name_map.insert(std::make_pair(bind::fname(rel), C5_rel_name));
		  m_c5_rel_name_to_rel_map.insert(std::make_pair(C5_rel_name, bind::fname(rel)));
		  rel_index ++;
	  }

	  //consider whether collecting integer constants in the rule is useful.
	  if (ICEMod) extractConstants(db);
	  //consider unknowns which are definitely not useful in invariant inference.
	  extractUnknowns(db);

	  //print the map from predicate name to C5-form predicate name
	  LOG("ice", errs() << "REL NAME TO C5 NAME MAP:\n";);
	  for(auto it = m_rel_to_c5_rel_name_map.begin(); it != m_rel_to_c5_rel_name_map.end(); ++it)
	  {
		  LOG("ice", errs() << *(it->first) << ", " << *(it->second) << "\n";);
	  }
  }

  //Set .names file and .interval file
  //Only set up for the predicate we want to re-Learn.
  void ICE::initC5(ExprVector targets)
  {
	  auto &db = m_hm.getHornClauseDB();
	  m_attr_name_to_expr_map.clear();
	  m_pred_name_to_expr_map.clear();

	  std::ofstream names_of(m_C5filename + ".names");
	  if(!names_of)return;
	  names_of << "invariant.\n";

	  //first attribute is the predicate names
	  names_of << "$pc: ";
	  int counter=0;
	  for(Expr rel : db.getRelations()) {
		  if(std::find(targets.begin(), targets.end(), bind::fname(rel)) != targets.end()) {
			  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
			  if(counter == targets.size()-1) names_of << *C5_rel_name << ".\n";
			  else names_of << *C5_rel_name << ",";
			  counter ++;
		  }
	  }

	  int lowerInterval = 2;
	  int upperInterval = 2;
	  std::ofstream intervals_of(m_C5filename + ".intervals");
	  if(!intervals_of)return;
	  //each argument of each predicate is an attribute
	  for(Expr rel : db.getRelations()) {
		  if(std::find(targets.begin(), targets.end(), bind::fname(rel)) != targets.end()) {
			  Expr C5_rel_name = m_rel_to_c5_rel_name_map.find(bind::fname(rel))->second;
			  for(int i=0; i<bind::domainSz(rel); i++) {
				  // if(isOpX<INT_TY>(bind::domainTy(rel, i)) || isOpX<BOOL_TY>(bind::domainTy(rel, i)))
				  if(isOpX<BVSORT>(bind::domainTy(rel, i)) || isOpX<INT_TY>(bind::domainTy(rel, i)) || isOpX<BOOL_TY>(bind::domainTy(rel, i))) {
				  	  LOG("ice", errs() << "BVSORT OR BOOL TYPE!\n";);
					  if (unknowns[rel][i]) // Exclude unknowns from invariant inference.
						  continue;
					  Expr arg_i_type = bind::domainTy(rel, i);
					  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
					  Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
					  m_attr_name_to_expr_map.insert(std::make_pair(attr_name_i, arg_i));
					  names_of << attr_name_i << ": continuous.\n";
					  upperInterval ++;
				  } else {
					  LOG("ice", errs() << "NOT BVSORT, INT OR BOOL TYPE!\n";);
				  }
			  }
			  //implicit attributes which have the form x % n.
			  if (ICEMod > 0 && !ruleConstants.empty()) {
				  for(int i=0; i<bind::domainSz(rel); i++) {
					  if (unknowns[rel][i]) // Exclude unknowns from invariant inference.
						  continue;
					  for (int cons : ruleConstants) {
						  if(isOpX<INT_TY>(bind::domainTy(rel, i))) {
							  Expr arg_i_type = bind::domainTy(rel, i);
							  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
							  Expr attr_name_i = variant::tag(C5_rel_name, bind::fname(bind::fname(arg_i)));
							  names_of << attr_name_i << "mod" << cons << ":= (" << attr_name_i << " % " << cons << " + " << cons << ") % " << cons << ".\n";
							  upperInterval ++;
						  }
					  }
				  }
			  }
			  //implicit attributes which have the form x1 +/- x2
			  if (ICEOct) {
			  for(int i=0; i<bind::domainSz(rel); i++) {
				  if (unknowns[rel][i]) // Exclude unknowns from invariant inference.
					  continue;
				  for(int j=i+1; j<bind::domainSz(rel); j++) {
					  if (unknowns[rel][j]) // Exclude unknowns from invariant inference.
						  continue;
					  if(isOpX<INT_TY>(bind::domainTy(rel, i)) && isOpX<INT_TY>(bind::domainTy(rel, j))) {
						  Expr arg_type = bind::domainTy(rel, i);
						  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_type));
						  Expr arg_j = bind::fapp(bind::constDecl(variant::variant(j, mkTerm<std::string> ("V", rel->efac ())), arg_type));
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
			  for(std::map<Expr, std::string>::iterator it = m_svmattr_name_to_str_map.begin(); it!= m_svmattr_name_to_str_map.end(); ++it) {
				  std::ostringstream ossA; ossA << *(it->first);
				  if (ossA.str().find(ossR.str()) != std::string::npos) {
					  // This is ineed realted to C5_rel_name
					  names_of << *(it->first) << ":= " << (it->second) << ".\n";
					  upperInterval ++;
				  }
			  }

			  std::string interval_line;
			  if(bind::domainSz(rel) == 0) {
				  interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval) + "\n";
			  } else {
				  interval_line = boost::lexical_cast<std::string>(lowerInterval) + " " + boost::lexical_cast<std::string>(upperInterval - 1) + "\n";
			  }
			  intervals_of << interval_line;
			  lowerInterval = upperInterval;
			  upperInterval = lowerInterval;
		  }
	  }

    names_of << "invariant: true, false.\n";
	  names_of.close();
	  intervals_of.close();
  }

  void ICE::C5learn(ExprVector targets)
  {
		errs() << "-------------------------C5Learn--------------------------\n";
		for (int i = 0; i < targets.size(); i++) { errs() << "target " << i << " : "<< blue << *targets[i] << normal << "\n"; }
	  initC5 (targets);
	  generateC5DataAndImplicationFiles(targets);
	  LOG("ice", errs() << "DATA & IMPL FILES ARE GENERATED\n";);

	  FILE *fp;
	  std::string command = C5ExecPath + " -I 1 -m 1 -f " + m_C5filename;
	  //std::string command = "/home/chenguang/Desktop/C50-ICE/C50/c5.0dbg -I 1 -m 1 -f " + m_C5filename;
	  std::string access = "r";
	  if((fp = popen(command.c_str(), access.c_str())) == NULL) { perror("popen failed!\n"); return; }

	  char buf[1024];
	  size_t status = fread(buf, sizeof(char), sizeof(buf), fp);
	  if(status == 0) { LOG("ice", errs() << "read from popen failed!\n";); return; }
	  pclose(fp);

	  FILE *wp;
	  wp = fopen("C5_temp","w+");
	  fwrite(buf, 1, sizeof(buf), wp);
	  fclose(wp);

	  //parse the .json file to ptree
	  std::ifstream if_json(m_C5filename + ".json");
	  std::ostringstream json_buf;
	  char ch;
	  while(json_buf && if_json.get(ch))
	  { json_buf.put(ch); }
	  if_json.close();

	  std::string json_string =  json_buf.str();

	  boost::property_tree::ptree pt;
	  std::stringstream ss(json_string);
	  try
	  { boost::property_tree::json_parser::read_json(ss, pt); }
	  catch(boost::property_tree::ptree_error & e)
	  { LOG("ice", errs() << "READ JSON ERROR!\n";); return; }

	  //parse ptree to invariant format
	  convertPtreeToInvCandidate(pt, targets);
	  auto &db = m_hm.getHornClauseDB();

	  extractFacts(db, targets);

	  //print the invariant map after this learning round
	  LOG("ice", errs() << "NEW CANDIDATES MAP:\n";);
	  for(Expr rel : db.getRelations()) {
		  LOG("ice", errs() << red << "relations : " << *rel << "\n" << normal;);
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++) {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand = m_candidate_model.getDef(fapp);
		  errs() << green << *fapp << normal << " : " << *cand << "\n";
	  }
  }



  // Collect unknowns in the rules
  void ICE::extractUnknowns(HornClauseDB &db) {
	  ExprVector pred_apps;
	  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it) {
		  HornRule r = *it;
	  	  pred_apps.push_back(r.head());
	  	  get_all_pred_apps(r.body(), db, std::back_inserter(pred_apps));
	  }

	  for (Expr app : pred_apps) {
		  Expr rel = bind::fname(app);
		  int size = bind::domainSz(rel);

		  auto it = unknowns.find(rel);
		  if (unknowns.end() == it) {
			  std::vector<bool> flags(size);
			  for (int i = 0; i < size; i++)
				  flags[i] = true;
			  unknowns[rel] = flags;
		  }

		  for(int i=0; i<bind::domainSz(rel); i++) {
			  Expr name = app->arg(i+1);
			  std::ostringstream oss;
			  oss << name;
			  if (oss.str().find("@unknown") != -1 || oss.str().find ("_nondet_") != -1) {
				  unknowns[rel][i] = false;
			  }
		  }
	  }

	  for(std::map<Expr, std::vector<bool>>::iterator itr =
			  unknowns.begin(); itr != unknowns.end(); ++itr) {
		  for (int i = 0; i < itr->second.size(); i++) {
			  itr->second[i] = !itr->second[i];
		  }
	  }
	  //LOG("ice", errs() << "Unknown search done.\n");
  }

  // Collect integers in the rules ...
  // Fixme. It seems we only need to consider mod operations.
  void ICE::extractConstants(HornClauseDB &db) {
	  struct IsREM : public std::unary_function<Expr, bool>
	  {
		  IsREM () {} 
	  	bool operator() (Expr e) {return isOpX<REM>(e);}
	  };

	  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it) {
		  HornRule r = *it;
		  ExprVector body_pred_apps;

		  filter (r.body(), IsREM(), std::back_inserter(body_pred_apps));

		  for (Expr p : body_pred_apps) {
			  Expr mod = p->right();
			  std::ostringstream oss;
			  oss << mod;
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
    ExprMap body_map;
    ExprVector body_pred_apps;
    get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));

    for (Expr p : body_pred_apps) {
    	if (p == t) {
    		if (s == NULL) body_map.insert (std::make_pair (p, mk<TRUE> (p->efac ())));
    		else body_map.insert (std::make_pair (p, s));
    	}
    	else body_map.insert (std::make_pair (p, m_candidate_model.getDef(p)));
    }
    Expr body_constraints = replace(ruleBody, body_map);
    return body_constraints;
  }


  //ice.genInitialCandidates(hm.getHornClauseDB());
  void ICE::genInitialCandidates (HornClauseDB &db)
  {
	  for(Expr rel : db.getRelations()) {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++) {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr True = mk<TRUE>(rel->efac());
		  Expr False = mk<FALSE>(rel->efac());

		  for (auto q : db.getQueries ()) {
			  Expr query = q.get();
			  if (bind::fname (query) == rel) m_candidate_model.addDef(fapp, False);
			  else m_candidate_model.addDef(fapp, True);
		  }
	  }

	  ExprVector empty;
	  extractFacts (db, empty);
  }


  // Match wheter an example corresponds to a fact.
  bool ICE::matchFacts (HornClauseDB &db, DataPoint p) {
	  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it)
	  {
		  HornRule r = *it;
		  if (isOpX<TRUE>(r.body()) && isOpX<FAPP>(r.head()) && p.getPredName() == bind::fname(bind::fname(r.head()))) {
			  Expr head = r.head();
			  Expr rel = bind::fname(head);
			  bool matched = false;
			  for(int i=0; i<bind::domainSz(rel); i++)
			  {
				  Expr arg_i_value = head->arg(i+1);
				  LOG("ice", errs() << *arg_i_value << ",";);
				  Expr arg_i_type = bind::domainTy(rel, i);
				  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));

				  if(isOpX<TRUE>(arg_i_value))
				  {
					  std::list<Expr>::iterator it = p.getAttrValues().begin();
					  std::advance(it, i);
					  LOG("ice", errs() << "(" <<**it << "),";);
					  std::ostringstream oss;
					  oss << **it;
					  if(oss.str().compare("1") == 0) {
					  //if(isOpX<TRUE>(*it)) {
						  matched = true;
					  } else {
						  matched = false;
						  break;
					  }
				  }
				  else if(isOpX<FALSE>(arg_i_value))
				  {
					  std::list<Expr>::iterator it = p.getAttrValues().begin();
					  std::advance(it, i);
					  LOG("ice", errs() << "(" <<**it << "),";);
					  std::ostringstream oss;
					  oss << **it;
					  if(oss.str().compare("0") == 0) {
					  //if(isOpX<FALSE>(*it)) {
						  matched = true;
					  } else {
						  matched = false;
						  break;
					  }
				  }
				  else if(bind::isBoolConst(arg_i_value))
				  {
					  matched = true;
				  }
				  else if(bind::isIntConst(arg_i_value))
				  {
					  matched = true;
				  }
				  else { /* Other kind of constructs in fact rules not implemented yet ...*/ }
			  }

			  if (matched) {
				  LOG("ice", errs() << "\nMatched!\n");
				  return true;
			  }
		  }
	  }

	  LOG("ice", errs() << "\nUnMatched!\n");
	  return false;
  }

  // Dealing with fact rules inside Horn System.
  // <1> Scan all the fact rules (true -> f (...)) <2>
  void ICE::extractFacts (HornClauseDB &db, ExprVector targets) {
	  LOG("ice", errs() << "Extracting Fact Rules ...\n");
	  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it) {
		  HornRule r = *it;
		  if (isOpX<TRUE>(r.body()) && isOpX<FAPP>(r.head())) {
			  Expr head = r.head();
			  Expr rel = bind::fname(head);

			  if (targets.empty() || std::find(targets.begin(), targets.end(), bind::fname(rel)) != targets.end()) {
				  ExprVector arg_list;
				  bool fact = false;
				  Expr currSolve = mk<TRUE>(rel->efac());
				  for(int i=0; i<bind::domainSz(rel); i++) {
					  Expr arg_i_value = head->arg(i+1);
					  LOG("ice", errs() << *arg_i_value << ",";);
					  Expr arg_i_type = bind::domainTy(rel, i);
					  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
					  arg_list.push_back(arg_i);

					  if(bind::isBoolConst(arg_i_value) || (bind::isIntConst(arg_i_value))
						  LOG("ice", errs() << "UNCERTAIN VALUE Don't Care: " << *arg_i_value << "\n";);
					  else if(isOpX<TRUE>(arg_i_value) && isOpX<FALSE>(arg_i_value)) {
						  fact = true;
					  	if(isOpX<FALSE>(arg_i_value)) currSolve = mk<AND>(currSolve, mk<NEG>(arg_i));
							else /* if(isOpX<TRUE>(arg_i_value)) */ currSolve = mk<AND>(currSolve, arg_i);
					  }
					  else { /* Other kind of constructs in fact rules not implemented yet ...*/ }
				  }

				  if (fact) {
					  // Add fact rules into solutions.
					  Expr fapp = bind::fapp(rel, arg_list);
					  Expr preSolve = m_candidate_model.getDef(fapp);
					  m_candidate_model.addDef(fapp, mk<OR>(preSolve, currSolve));
				  }
			  }
		  }
	  }
	  LOG("ice", errs() << "Extracted Fact Rules.\n");
  }


  bool ICE::generatePostiveSamples (HornClauseDB &db, HornRule r, ZSolver<EZ3> solver, int& index, bool& run) {
	  Expr body_app = r.head();
	  if (bind::domainSz(bind::fname(body_app)) <= 0) {
		  LOG ("ice", errs () << "Rule cannot be refined.\n");
		  exit (-3);
	  }

	  Expr r_head_cand = m_candidate_model.getDef(r.head());
	  LOG("ice", errs() << "TRYING TO ADD some CounterExample.\n";);

	  solver.reset();
	  solver.assertExpr(mk<NEG>(r_head_cand));
	  Expr body_forumla = extractRelation(r, db, NULL, NULL);
	  LOG ("ice", errs() << "Verification condition: " << bold << cyan << *r_head_cand << " <- " << *body_forumla << normal << "\n");
	  solver.assertExpr(body_forumla);

	  //solver.toSmtLib(errs());
	  boost::tribool result = solver.solve();
	  if(result != UNSAT) {
		  LOG("ice", errs() << "SAT, NEED TO ADD More Examples\n";);
		  //get cex
		  ZModel<EZ3> m = solver.getModel();
		  //print cex
		  LOG("ice", errs() << "(";);
		  LOG("ice", errs() << ") -> (";);
		  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++) {
			  Expr arg_i = body_app->arg(i+1);
			  Expr arg_i_value = m.eval(arg_i);
			  LOG("ice", errs() << *arg_i_value << ",";);
		  }
		  LOG("ice", errs() << ")\n";);

		  //add counterexample
		  std::list<Expr> attr_values;
		  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++) {
			  Expr arg_i = body_app->arg(i+1);
			  Expr arg_i_value = m.eval(arg_i);

			  //deal with uncertain values in cexs
			  if(bind::isBoolConst(arg_i_value)) {
				  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
				  Expr uncertain_value = mk<FALSE>(arg_i_value->efac());
				  arg_i_value = uncertain_value;
			  } else if(bind::isIntConst(arg_i_value)) {
				  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
				  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
				  arg_i_value = uncertain_value;
			  }

			  //convert true/false to 1/0 in C5 data point
			  if(isOpX<TRUE>(arg_i_value))
				  arg_i_value = mkTerm<mpz_class>(1, arg_i_value->efac());
			  else if(isOpX<FALSE>(arg_i_value))
				  arg_i_value = mkTerm<mpz_class>(0, arg_i_value->efac());

			  //deal with too large integer value like: -0xffffffb
			  std::ostringstream oss;
			  oss << arg_i_value;
			  if(oss.str().find("-0x") == 0) {
				  LOG("ice", errs() << "TOO LARGE VALUE, OVERFLOW: " << *arg_i_value << "\n";);
				  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
				  arg_i_value = uncertain_value;
			  }

			  attr_values.push_back(arg_i_value);
		  }

		  DataPoint pos_dp(bind::fname(bind::fname(body_app)), attr_values);
		  int orig_size = m_pos_data_set.size();
		  addPosCex(pos_dp);
		  if(m_pos_data_set.size() == orig_size + 1) //no duplicate
		  {
			  if (SVMExecPath.compare("") != 0 && m_neg_data_set.size() > /*50*/ICESVMFreqPos) {
				  LOG("ice", errs() << "SVM based Hyperlane Learning!\n");
				  svmLearn (NULL);
			  }
			  if (!ICEICE) {
			  m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(),
					  [pos_dp,body_app,this](DataPoint p) {
				  	  	  return p.getPredName() == bind::fname(bind::fname(body_app))
				  	  	  	  	  && m_neg_data_set.find(p) != m_neg_data_set.end();
				  	  	  //return p == pos_dp;
			  	  	  }), m_cex_list.end());
			  //m_neg_data_set.erase(std::remove_if(m_neg_data_set.begin(), m_neg_data_set.end(),
			  //		  [body_app](DataPoint p) {
			  //	  	  	  return p.getPredName() == bind::fname(bind::fname(body_app)); }), m_neg_data_set.end());
			  for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
				  if (it->getPredName() == bind::fname(bind::fname(body_app))) {
				  //if (*it == pos_dp) {
					  m_neg_data_set.erase (it++);
				  } else {
					  ++it;
				  }
			  }
			  m_neg_data_count.erase (pos_dp.getPredName());
			  }
			  m_cex_list.push_back(pos_dp);
			  addDataPointToIndex(pos_dp, index);
			  LOG("ice", errs() << "POS CEX, INDEX IS " << index << "\n";);
			  index++;

			  run = sampleLinearHornCtrs(body_app, pos_dp, index);
		  }
		  else //it is a duplicate data point
		  {
			  LOG("ice", errs() << "Duplicated positive points should be impossible.\n");
			  exit (-3);
		  }

		  return true;
	  } else {
		  return false;
	  }
  }
	}

  // Given a rule head, extract all rules using it in body, then add all such rules to the beginning of workList
  void addUsedToWorkList(HornClauseDB &db, std::list<HornRule> &workList, HornRule r)
  {
  	  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it)
  	  {
  		  if(*it == r)
  		  {
  			  continue;
  		  }
  		  HornRule rule = *it;
  		  Expr r_body = rule.body();
  		  ExprVector body_pred_apps;
  		  get_all_pred_apps(r_body, db, std::back_inserter(body_pred_apps));

  		  for (Expr body_pred_app : body_pred_apps) {
  			  if (bind::fname(body_pred_app) == bind::fname(r.head())) {
  	  			  if(std::find(workList.begin(), workList.end(), *it) == workList.end())
  	  			  {
  	  				  workList.push_front(*it);
  	  			  }
  	  			  break;
  			  }
  		  }
  	  }
  }

  // Given a rule, extract all rules using its body_apps in head, then add all such rules to the end of workList
  void addNewToWorkList (HornClauseDB &db, std::list<HornRule> &workList, HornRule r) {
	  Expr r_body = r.body();
	  ExprVector body_pred_apps;
	  get_all_pred_apps(r_body, db, std::back_inserter(body_pred_apps));

	  for(auto it = db.getRules().begin(); it != db.getRules().end(); ++it)
	  {
		  if(*it == r)
		  {
			  continue;
		  }
		  HornRule rule = *it;
		  for (Expr body_pred_app : body_pred_apps) {
			  if (bind::fname(body_pred_app) == bind::fname(rule.head())) {
				  if(std::find(workList.begin(), workList.end(), *it) == workList.end())
				  {
					  workList.push_back(*it);
				  }
				  break;
			  }
		  }
	  }
  }

static int solveConstraintTime = 0;
  bool ICE::solveConstraints(HornClauseDB &db, bool &isChanged, int &index)
  {
  	solveConstraintTime++;
	  std::list<HornRule> workList;
	  workList.insert(workList.end(), db.getRules().begin(), db.getRules().end());
	  workList.reverse();

  	LOG("ice", errs() << "=========================== Constraint Solving of Horn Clauses ============================\n";);
	  ZSolver<EZ3> solver(m_hm.getZContext());

	  int loopi = 0;
	  while (!workList.empty())
	  {
	  	LOG ("ice", errs() << bold << yellow << " solveConstraint #" << solveConstraintTime << " --- LOOP #" << ++loopi << " times ---\n" << normal);
		  HornRule r = workList.front();
		  workList.pop_front();
		  // HornRule r = *it;

		  LOG("ice", errs() << red << "VERIFY Horn Rule: " << normal << *(r.head()) << " <- " << *(r.body()) << "\n";);

		  bool upd = false; int counter = 0; bool posUpd = false;

		  Expr r_body = r.body();
		  ExprVector body_pred_apps;
		  get_all_pred_apps(r_body, db, std::back_inserter(body_pred_apps));


		  bool cleanBody = true;
		  for (Expr body_app : body_pred_apps) {
			  if (bind::domainSz(bind::fname(body_app)) <= 0) {
				  // This is clean.
				  // cleanBody = true;
			  } else {
				  cleanBody = false;
				  break;
			  }
		  }

		  if (body_pred_apps.size() <= 0 || cleanBody) {
				  // bind::domainSz(bind::fname(body_pred_apps[0])) <= 0) {
			  if (bind::domainSz(bind::fname(r.head ())) <= 0) {
				  LOG ("ice", errs() << "Verify a rule without unknown invariants.\n");
				  Expr r_head_cand = m_candidate_model.getDef(r.head());
				  solver.reset();
				  solver.assertExpr(mk<NEG>(r_head_cand));
				  Expr body_forumla = extractRelation(r, db, NULL, NULL);
				  LOG ("ice", errs() << "Verification condition: " << *r_head_cand << " <- " << *body_forumla << "\n");
				  solver.assertExpr(body_forumla);
				  boost::tribool result = solver.solve();
				  if(result != UNSAT) {
					  outs()<<"Program is buggy.\n";
					  std::list<Expr> attr_values;
					  DataPoint pos_dp(bind::fname(bind::fname(r.head())), attr_values);
					  addPosCex(pos_dp);
					  failurePoint = m_pos_list.size()-1;
					  return false;
				  }
			  } else {
				  // Head is possibly need to be refined!
				  LOG ("ice", errs() << cyan << "Generate Initial Program State Samples.\n" << normal);
				  do {
					  bool run = true;
					  upd = generatePostiveSamples (db, r, solver, index, run);
					  if (!run) return false;
					  if (upd) {
						  isChanged = true; posUpd = true;
						  // Which predicates will be changed in this iteration of solving.
						  ExprVector changedPreds;
						  // FixMe. Bad Code.
						  changedPreds.push_back (bind::fname(*(db.getRelations().begin())));
						  changedPreds.push_back(bind::fname(bind::fname(r.head())));
							C5learn (changedPreds);
					  }
				  } while (upd);
				  // --- Extend work list as we just go through a strengthening loop ----
				  addUsedToWorkList (db, workList, r);
			  }
		  } else {
			  //Expr body_app = body_pred_apps[0];
			  //Expr preSolve = m_candidate_model.getDef(body_app);
			  if (ICELocalStrengthen) {
			  HornDbModel global_cache;
			  for (Expr body_app : body_pred_apps) {
				  ExprVector arg_list;
				  Expr rel = bind::fname (body_app);
				  for(int i=0; i<bind::domainSz(rel); i++) {
					  Expr arg_i_type = bind::domainTy(rel, i);
					  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
					  arg_list.push_back(arg_i);
				  }
				  Expr fapp = bind::fapp(rel, arg_list);
				  global_cache.addDef(fapp, m_candidate_model.getDef(fapp));
			  }
			  do {
				  // Only strengthen the lhs, keeping rhs unchanged.
				  // Save what rhs is.
				  Expr r_head = r.head();
				  Expr r_head_cand = m_candidate_model.getDef(r_head);
				  {
					  solver.reset();
					  solver.assertExpr(mk<NEG>(r_head_cand));
					  Expr body_forumla = extractRelation(r, db, NULL, NULL);
					  solver.assertExpr(body_forumla);
					  boost::tribool result = solver.solve();
					  if(result == UNSAT) { // Successfully prove the rule with current solution.
						  LOG("ice", errs() << "-- Finally the rule is proved at counter " << counter << "!\n");
						  break;
				  	  }
				  }

				  // Save previous solution of lhs.
				  // After the following do-while, update solution of lhs conjoining the previous solution
				  HornDbModel local_cache;
				  for (Expr body_app : body_pred_apps) {
					  ExprVector arg_list;
					  Expr rel = bind::fname (body_app);
					  for(int i=0; i<bind::domainSz(rel); i++)
					  {
						  Expr arg_i_type = bind::domainTy(rel, i);
						  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
						  arg_list.push_back(arg_i);
					  }
					  Expr fapp = bind::fapp(rel, arg_list);
					  local_cache.addDef(fapp, m_candidate_model.getDef(fapp));
				  }

				  do {
					  counter ++;
					  LOG("ice", errs() << "Rule Verification Round " << counter << "\n");

					  // Which predicates will be changed in this iteration of solving.
					  ExprVector changedPreds;
					  changedPreds.push_back (bind::fname(*(db.getRelations().begin())));


					  upd = false;
					  //Expr r_head = r.head();
					  //Expr r_head_cand = m_candidate_model.getDef(r_head);

					  LOG("ice", errs() << "TRYING TO ADD some CounterExample.\n";);
					  solver.reset();
					  solver.assertExpr(mk<NEG>(r_head_cand));
					  Expr body_forumla = extractRelation(r, db, NULL, NULL);
					  solver.assertExpr(body_forumla);
					  LOG ("ice", errs() << yellow << "Verification condition: " << *r_head_cand << " <- " << *body_forumla << "\n" << normal);

					  solver.toSmtLib(errs() << cyan);
					  errs() << normal;

					  boost::tribool result = solver.solve();
					  if(result != UNSAT) {
						  LOG("ice", errs() << "SAT, NEED TO ADD The Counterexample\n";);
						  upd = true; isChanged = true;
						  //get cex
						  ZModel<EZ3> m = solver.getModel();
						  //print cex
						  std::set<DataPoint> negPoints;
						  for (Expr body_app : body_pred_apps) {
							  if (bind::domainSz(bind::fname(body_app)) <= 0)
								  // No counterexample can be obtained from it because it is clean.
								  continue;

							  LOG("ice", errs() << "(";);
							  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++) {
								  Expr arg_i = body_app->arg(i+1);
								  Expr arg_i_value = m.eval(arg_i);
								  LOG("ice", errs() << *arg_i_value << ",";);
							  }
							  LOG("ice", errs() << ") -> (";);
							  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++) {
								  Expr arg_i = r_head->arg(i+1);
								  Expr arg_i_value = m.eval(arg_i);
								  LOG("ice", errs() << *arg_i_value << ",";);
							  }
							  LOG("ice", errs() << ")\n";);

							  // Presumbaly add counterexample
							  std::list<Expr> attr_values;
							  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++) {
								  Expr arg_i = body_app->arg(i+1);
								  Expr arg_i_value = m.eval(arg_i);

								  //deal with uncertain values in cexs
								  if(bind::isBoolConst(arg_i_value)) {
									  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mk<FALSE>(arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  } else if(bind::isIntConst(arg_i_value)) {
									  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }

								  //convert true/false to 1/0 in C5 data point
								  if(isOpX<TRUE>(arg_i_value))
									  arg_i_value = mkTerm<mpz_class>(1, arg_i_value->efac());
								  else if(isOpX<FALSE>(arg_i_value))
									  arg_i_value = mkTerm<mpz_class>(0, arg_i_value->efac());

								  //deal with too large integer value like: -0xffffffb
								  std::ostringstream oss;
								  oss << arg_i_value;
								  if(oss.str().find("-0x") == 0) {
									  LOG("ice", errs() << "TOO LARGE VALUE, OVERFLOW: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }

								  attr_values.push_back(arg_i_value);
							  }

							  // If the counterexample is already labeled positive;
							  // Add its successive (aka. state transition) to positives instead.
							  DataPoint neg_dp(bind::fname(bind::fname(body_app)), attr_values);
							  negPoints.insert(neg_dp);
						  }

						  bool foundPos = true;
						  for (DataPoint neg_dp : negPoints) {
							  auto searched = m_pos_data_set.find(neg_dp);
							  if (searched != m_pos_data_set.end() || matchFacts (db, neg_dp)) {
								  // Found it in positive samples!
								  // foundPos = true;
							  } else {
								  foundPos = false;
								  break;
							  }
						  }
						  //auto searched = m_pos_data_set.find(neg_dp);
						  //if (searched != m_pos_data_set.end()) {
						  if (foundPos) {
							  if (bind::domainSz(bind::fname(r_head)) <= 0) {
								  outs()<<"Program is buggy.\n";
			  	  	  	std::list<Expr> attr_values;
								  DataPoint pos_dp(bind::fname(bind::fname(r.head())), attr_values);
								  addPosCex(pos_dp);
								  failurePoint = m_pos_list.size()-1;
								  std::list<int> preIndices;
								  for (DataPoint neg_dp : negPoints) {
									  auto searched = m_pos_data_set.find(neg_dp);
									  if (searched != m_pos_data_set.end()) {
										  preIndices.push_back(m_pos_index_map[neg_dp]);
									  }
								  }
								  postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));
								  return false;
							  }

							  std::list<Expr> attr_values;
							  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++) {
								  Expr arg_i = r_head->arg(i+1);
								  Expr arg_i_value = m.eval(arg_i);

								  //deal with uncertain values in cexs
								  if(bind::isBoolConst(arg_i_value)) {
									  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mk<FALSE>(arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  } else if(bind::isIntConst(arg_i_value)) {
									  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }

								  //convert true/false to 1/0 in C5 data point
								  if(isOpX<TRUE>(arg_i_value))
									  arg_i_value = mkTerm<mpz_class>(1, arg_i_value->efac());
								  else if(isOpX<FALSE>(arg_i_value))
									  arg_i_value = mkTerm<mpz_class>(0, arg_i_value->efac());

								  //deal with too large integer value like: -0xffffffb
								  std::ostringstream oss;
								  oss << arg_i_value;
								  if(oss.str().find("-0x") == 0) {
									  LOG("ice", errs() << "TOO LARGE VALUE, OVERFLOW: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }

								  attr_values.push_back(arg_i_value);
							  }
							  DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
							  int orig_size = m_pos_data_set.size();
							  addPosCex(pos_dp);
							  if(m_pos_data_set.size() == orig_size + 1) //no duplicate
							  {
								  if (SVMExecPath.compare("") != 0 && m_neg_data_set.size() > /*50*/ICESVMFreqPos) {
									  LOG("ice", errs() << "SVM based Hyperlane Learning!\n");
									  svmLearn (NULL);
								  }

								  m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(),
										  [pos_dp,r_head,this](DataPoint p) {
											  return p.getPredName() == bind::fname(bind::fname(r_head)) && m_neg_data_set.find(p) != m_neg_data_set.end();
								  	  	  }), m_cex_list.end());
								  for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
									  if (it->getPredName() == bind::fname(bind::fname(r_head))) {
										  m_neg_data_set.erase (it++);
									  } else {
										  ++it;
									  }
								  }
								  m_neg_data_count.erase (pos_dp.getPredName());

								  // ---- Clean negative samples for body apps as well
								  for (Expr body_app : body_pred_apps) {
									  if (bind::domainSz(bind::fname(body_app)) <= 0)
										  continue;

									  m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(),
											  [body_app,this](DataPoint p) {
												  return p.getPredName() == bind::fname(bind::fname(body_app))
														  && m_neg_data_set.find(p) != m_neg_data_set.end();
											  }), m_cex_list.end());
									  for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
										  if (it->getPredName() == bind::fname(bind::fname(body_app))) {
											  m_neg_data_set.erase (it++);
										  } else {
											  ++it;
										  }
									  }
									  m_neg_data_count.erase (bind::fname(bind::fname(body_app)));
								  }
								  // ---- Doubly check if the above code is necessary

								  m_cex_list.push_back(pos_dp);
								  addDataPointToIndex(pos_dp, index);
			  	  	  	std::list<int> preIndices;
			  	  	  	for (DataPoint neg_dp : negPoints) {
									  auto searched = m_pos_data_set.find(neg_dp);
									  if (searched != m_pos_data_set.end()) {
										  preIndices.push_back(m_pos_index_map[neg_dp]);
									  }
								  }
			  	  	  	postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));

								  LOG("ice", errs() << "POS CEX, INDEX IS " << index << "\n";);
								  index++;
								  posUpd = true;

								  bool run = sampleLinearHornCtrs(r_head, pos_dp, index);
			  	  	  	if (!run) return false;

								  changedPreds.push_back(pos_dp.getPredName());
							  } else //it is a duplicate data point {
								  LOG("ice", errs() << "Duplicated positive points should be impossible.\n");
								  exit (-3);
							  }
						  } else {
							  for (DataPoint neg_dp : negPoints) {
								  auto searched = m_pos_data_set.find(neg_dp);
								  if (searched != m_pos_data_set.end() || matchFacts (db, neg_dp)) {
									  // Found this in positive set.
								  } else {
									  int orig_size = m_neg_data_set.size();
									  addNegCex(neg_dp);
									  if(m_neg_data_set.size() == orig_size + 1) //no duplicate
									  {
										  m_cex_list.push_back(neg_dp);
										  addDataPointToIndex(neg_dp, index);
										  LOG("ice", errs() << "NEG CEX, INDEX IS " << index << "\n";);
										  index++;

										  if (changedPreds.size() <= 1 || std::find(changedPreds.begin(), changedPreds.end(), neg_dp.getPredName()) == changedPreds.end())
											  changedPreds.push_back(neg_dp.getPredName());

										  if (SVMExecPath.compare("") != 0) {
											  std::map<Expr, int>::iterator it = m_neg_data_count.find(neg_dp.getPredName());
											  if (it != m_neg_data_count.end() && it->second > ICESVMFreqNeg && it->second % ICESVMFreqNeg == 0) {
												  LOG("ice", errs() << "SVM based Hyperplane Learning!\n");
												  svmLearn (neg_dp.getPredName());
											  }
										  }
									  }
									  else //it is a duplicate data point
									  {
										  LOG("ice", errs() << "Duplicated negative points should be impossible.\n");
										  exit (-3);
									  }
								  }
							  }
						  }
					  }

					  if (upd) {
						  // Ask machine learning for a new invariant for body_app.
						  // Expr pre = m_candidate_model.getDef(body_app);
						  //if (SVMExecPath.compare("") == 0)
							  C5learn (changedPreds);
							  if (posUpd) { break; }
							  else
								  for (Expr body_app : body_pred_apps) {
									  if (std::find(changedPreds.begin(), changedPreds.end(), bind::fname(bind::fname(body_app))) == changedPreds.end()) {
									  } else {
										  ExprVector arg_list;
										  Expr rel = bind::fname (body_app);
										  for(int i=0; i<bind::domainSz(rel); i++) {
											  Expr arg_i_type = bind::domainTy(rel, i);
											  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
											  arg_list.push_back(arg_i);
										  }
										  Expr fapp = bind::fapp(rel, arg_list);

										  Expr preSolve = local_cache.getDef(fapp);
										  Expr currSolve = m_candidate_model.getDef(fapp);
										  m_candidate_model.addDef(fapp, mk<AND>(preSolve, currSolve));
									  }
								  }
					  }
				  } while (upd);
			  } while (true);
		  	  } else {
			  do {
				  counter ++;
				  LOG("ice", errs() << "Rule Verification Round " << counter << "\n");

				  // Which predicates will be changed in this iteration of solving.
				  ExprVector changedPreds;
				  // FixMe. Bad Code.
				  //if (SVMExecPath.compare("") == 0) {
				  	  changedPreds.push_back (bind::fname(*(db.getRelations().begin())));

				  upd = false;
				  Expr r_head = r.head();
				  Expr r_head_cand = m_candidate_model.getDef(r_head);
				  LOG("ice", errs() << "TRYING TO ADD some CounterExample.\n";);
				  solver.reset();
				  solver.assertExpr(mk<NEG>(r_head_cand));
				  Expr body_forumla = extractRelation(r, db, NULL, NULL);
				  LOG ("ice", errs() << "Verification condition: " << *r_head_cand << " <- " << *body_forumla << "\n");
				  solver.assertExpr(body_forumla);

				  //solver.toSmtLib(errs());
				  boost::tribool result = solver.solve();
				  if(result != UNSAT) {
					  LOG("ice", errs() << "SAT, NEED TO ADD The Counterexample\n";);
					  upd = true; isChanged = true;
					  //get cex
					  ZModel<EZ3> m = solver.getModel();
					  //print cex
					  std::set<DataPoint> negPoints;
					  for (Expr body_app : body_pred_apps) {
						  if (bind::domainSz(bind::fname(body_app)) <= 0)
							  // No counterexample can be obtained from it because it is clean.
							  continue;

						  LOG("ice", errs() << "(";);
						  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++) {
							  Expr arg_i = body_app->arg(i+1);
							  Expr arg_i_value = m.eval(arg_i);
							  LOG("ice", errs() << *arg_i_value << ",";);
						  }
						  LOG("ice", errs() << ") -> (";);
						  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++) {
							  Expr arg_i = r_head->arg(i+1);
							  Expr arg_i_value = m.eval(arg_i);
							  LOG("ice", errs() << *arg_i_value << ",";);
						  }
						  LOG("ice", errs() << ")\n";);

						  // Presumbaly add counterexample
						  std::list<Expr> attr_values;
						  for(int i=0; i<bind::domainSz(bind::fname(body_app)); i++) {
							  Expr arg_i = body_app->arg(i+1);
							  Expr arg_i_value = m.eval(arg_i);

							  //deal with uncertain values in cexs
							  if(bind::isBoolConst(arg_i_value)) {
								  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
								  Expr uncertain_value = mk<FALSE>(arg_i_value->efac());
								  arg_i_value = uncertain_value;
							  } else if(bind::isIntConst(arg_i_value)) {
								  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
								  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
								  arg_i_value = uncertain_value;
							  }

							  //convert true/false to 1/0 in C5 data point
							  if(isOpX<TRUE>(arg_i_value)) {
								  arg_i_value = mkTerm<mpz_class>(1, arg_i_value->efac());
							  } else if(isOpX<FALSE>(arg_i_value)) {
								  arg_i_value = mkTerm<mpz_class>(0, arg_i_value->efac());
							  }

							  //deal with too large integer value like: -0xffffffb
							  std::ostringstream oss;
							  oss << arg_i_value;
							  if(oss.str().find("-0x") == 0) {
								  LOG("ice", errs() << "TOO LARGE VALUE, OVERFLOW: " << *arg_i_value << "\n";);
								  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
								  arg_i_value = uncertain_value;
							  }

							  attr_values.push_back(arg_i_value);
						  }

						  // If the counterexample is already labeled positive;
						  // Add its successive (aka. state transition) to positives instead.
						  DataPoint neg_dp(bind::fname(bind::fname(body_app)), attr_values);
						  negPoints.insert(neg_dp);
					  }

					  bool foundPos = true;
					  for (DataPoint neg_dp : negPoints) {
						  auto searched = m_pos_data_set.find(neg_dp);
						  if (searched != m_pos_data_set.end() || matchFacts (db, neg_dp)) {
							  // Found it in positive samples!
							  // foundPos = true;
						  } else {
							  foundPos = false;
							  break;
						  }
					  }
					  //auto searched = m_pos_data_set.find(neg_dp);
					  //if (searched != m_pos_data_set.end()) {
					  if (foundPos) {
						  if (bind::domainSz(bind::fname(r_head)) <= 0) {
							  outs()<<"Program is buggy.\n";
							  std::list<Expr> attr_values;
							  DataPoint pos_dp(bind::fname(bind::fname(r.head())), attr_values);
							  addPosCex(pos_dp);
							  failurePoint = m_pos_list.size()-1;
							  std::list<int> preIndices;
							  for (DataPoint neg_dp : negPoints) {
								  auto searched = m_pos_data_set.find(neg_dp);
								  if (searched != m_pos_data_set.end()) {
									  preIndices.push_back(m_pos_index_map[neg_dp]);
								  }
							  }
							  postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));
							  return false;
						  }

						  std::list<Expr> attr_values;
						  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++)
						  {
							  Expr arg_i = r_head->arg(i+1);
							  Expr arg_i_value = m.eval(arg_i);

							  //deal with uncertain values in cexs
							  if(bind::isBoolConst(arg_i_value))
							  {
								  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
								  Expr uncertain_value = mk<FALSE>(arg_i_value->efac());
								  arg_i_value = uncertain_value;
							  }
							  else if(bind::isIntConst(arg_i_value))
							  {
								  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
								  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
								  arg_i_value = uncertain_value;
							  }

							  //convert true/false to 1/0 in C5 data point
							  if(isOpX<TRUE>(arg_i_value))
							  {
								  arg_i_value = mkTerm<mpz_class>(1, arg_i_value->efac());
							  }
							  else if(isOpX<FALSE>(arg_i_value))
							  {
								  arg_i_value = mkTerm<mpz_class>(0, arg_i_value->efac());
							  }

							  //deal with too large integer value like: -0xffffffb
							  std::ostringstream oss;
							  oss << arg_i_value;
							  if(oss.str().find("-0x") == 0)
							  {
								  LOG("ice", errs() << "TOO LARGE VALUE, OVERFLOW: " << *arg_i_value << "\n";);
								  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
								  arg_i_value = uncertain_value;
							  }

							  attr_values.push_back(arg_i_value);
						  }
						  DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
						  int orig_size = m_pos_data_set.size();
						  addPosCex(pos_dp);
						  if(m_pos_data_set.size() == orig_size + 1) //no duplicate
						  {
							  if (SVMExecPath.compare("") != 0 && m_neg_data_set.size() > /*50*/ICESVMFreqPos) {
								  LOG("ice", errs() << "SVM based Hyperlane Learning!\n");
								  svmLearn (NULL);
							  }
							  if (!ICEICE) {
							  m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(),
									  [pos_dp,r_head,this](DataPoint p) {
										  return p.getPredName() == bind::fname(bind::fname(r_head))
										  		  && m_neg_data_set.find(p) != m_neg_data_set.end();
								  	  	  //return p == pos_dp;
							  	  	  }), m_cex_list.end());
							  //m_neg_data_set.erase(std::remove_if(m_neg_data_set.begin(), m_neg_data_set.end(),
							  //		  [r_head](DataPoint p) {
							  //			  return p.getPredName() == bind::fname(bind::fname(r_head)); }), m_neg_data_set.end());
							  for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
								  if (it->getPredName() == bind::fname(bind::fname(r_head))) {
								  //if (*it == pos_dp) {
									  m_neg_data_set.erase (it++);
								  } else {
									  ++it;
								  }
							  }
							  m_neg_data_count.erase (pos_dp.getPredName());

							  // ---- Clean negative samples for body apps as well
							  for (Expr body_app : body_pred_apps) {
								  if (bind::domainSz(bind::fname(body_app)) <= 0)
									  continue;

								  m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(),
										  [body_app,this](DataPoint p) {
											  return p.getPredName() == bind::fname(bind::fname(body_app))
													  && m_neg_data_set.find(p) != m_neg_data_set.end();
											  //return p == pos_dp;
										  }), m_cex_list.end());
								  //m_neg_data_set.erase(std::remove_if(m_neg_data_set.begin(), m_neg_data_set.end(),
								  //		  [r_head](DataPoint p) {
								  //			  return p.getPredName() == bind::fname(bind::fname(r_head)); }), m_neg_data_set.end());
								  for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
									  if (it->getPredName() == bind::fname(bind::fname(body_app))) {
									  //if (*it == pos_dp) {
										  m_neg_data_set.erase (it++);
									  } else {
										  ++it;
									  }
								  }
								  m_neg_data_count.erase (bind::fname(bind::fname(body_app)));
							  }
							  // ---- Doubly check if the above code is necessary
							  }
							  m_cex_list.push_back(pos_dp);
							  addDataPointToIndex(pos_dp, index);

							  std::list<int> preIndices;
							  for (DataPoint neg_dp : negPoints) {
								  auto searched = m_pos_data_set.find(neg_dp);
								  if (searched != m_pos_data_set.end()) {
									  preIndices.push_back(m_pos_index_map[neg_dp]);
							  	  }
							  }
							  postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));

							  LOG("ice", errs() << "POS CEX, INDEX IS " << index << "\n";);
							  index++;
							  posUpd = true;

							  bool run = sampleLinearHornCtrs(r_head, pos_dp, index);
							  if (!run) return false;

							  changedPreds.push_back(pos_dp.getPredName());
						  } else //it is a duplicate data point {
							  LOG("ice", errs() << "Duplicated positive points should be impossible.\n");
							  exit (-3);
						  }
					  } else {
						  bool surebad = false;
						  if (ICEICE) {
							  if (negPoints.size() > 1) {
								  errs() << "ICE learning is not suitable for this program.\n";
								  exit (-3);
							  }
							  if (bind::domainSz(bind::fname(r_head)) <= 0) surebad = true;
						  }
						  if (ICEICE && !surebad && negPoints.size() == 1) {
							  // Add Implication samples.
							  std::list<Expr> attr_values;
							  for(int i=0; i<bind::domainSz(bind::fname(r_head)); i++)
							  {
								  Expr arg_i = r_head->arg(i+1);
								  Expr arg_i_value = m.eval(arg_i);

								  //deal with uncertain values in cexs
								  if(bind::isBoolConst(arg_i_value))
								  {
									  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mk<FALSE>(arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }
								  else if(bind::isIntConst(arg_i_value))
								  {
									  LOG("ice", errs() << "UNCERTAIN VALUE: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }

								  //convert true/false to 1/0 in C5 data point
								  if(isOpX<TRUE>(arg_i_value))
								  {
									  arg_i_value = mkTerm<mpz_class>(1, arg_i_value->efac());
								  }
								  else if(isOpX<FALSE>(arg_i_value))
								  {
									  arg_i_value = mkTerm<mpz_class>(0, arg_i_value->efac());
								  }

								  //deal with too large integer value like: -0xffffffb
								  std::ostringstream oss;
								  oss << arg_i_value;
								  if(oss.str().find("-0x") == 0)
								  {
									  LOG("ice", errs() << "TOO LARGE VALUE, OVERFLOW: " << *arg_i_value << "\n";);
									  Expr uncertain_value = mkTerm<mpz_class>(0, arg_i_value->efac());
									  arg_i_value = uncertain_value;
								  }

								  attr_values.push_back(arg_i_value);
							  }
							  DataPoint pos_dp(bind::fname(bind::fname(r_head)), attr_values);
							  for (DataPoint neg_dp : negPoints) {
								  if (neg_dp.getPredName() != pos_dp.getPredName()) {
									  errs() << "ICE learning is not suitable for this program.\n";
									  exit (-3);
								  }
								  if(m_impl_cex_set.count(neg_dp) == 0)
								  {
									  addImplCex(neg_dp);
									  m_cex_list.push_back(neg_dp);
									  addDataPointToIndex(neg_dp, index);
									  LOG("ice", errs() << "IMPL CEX, INDEX IS " << index << "\n";);
									  index++;
								  }
								  if(m_impl_cex_set.count(pos_dp) == 0)
								  {
									  addImplCex(pos_dp);
									  m_cex_list.push_back(pos_dp);
									  addDataPointToIndex(pos_dp, index);
									  LOG("ice", errs() << "IMPL CEX, INDEX IS " << index << "\n";);
									  index++;
								  }
								  addImplPair(std::make_pair(neg_dp, pos_dp));
								  changedPreds.push_back(neg_dp.getPredName());
							  }
						  }
						  else
						  for (DataPoint neg_dp : negPoints) {
							  auto searched = m_pos_data_set.find(neg_dp);
							  if (searched != m_pos_data_set.end() || matchFacts (db, neg_dp)) {
								  // Found this in positive set.
							  } else {
								  int orig_size = m_neg_data_set.size();
								  addNegCex(neg_dp);
								  if(m_neg_data_set.size() == orig_size + 1) //no duplicate
								  {
									  m_cex_list.push_back(neg_dp);
									  addDataPointToIndex(neg_dp, index);
									  LOG("ice", errs() << "NEG CEX, INDEX IS " << index << "\n";);
									  index++;

									  if (changedPreds.size() <= 1 ||
											  std::find(changedPreds.begin(), changedPreds.end(), neg_dp.getPredName()) == changedPreds.end())
										  changedPreds.push_back(neg_dp.getPredName());

									  if (SVMExecPath.compare("") != 0)
											  //&& m_neg_data_set.size() > 100 && m_neg_data_set.size() % 100 == 0) {
									  {
										  std::map<Expr, int>::iterator it = m_neg_data_count.find(neg_dp.getPredName());
										  if (it != m_neg_data_count.end() && it->second > ICESVMFreqNeg && it->second % ICESVMFreqNeg == 0) {
											  LOG("ice", errs() << "SVM based Hyperplane Learning!\n");
											  svmLearn (neg_dp.getPredName());
										  }
									  }
								  }
								  else //it is a duplicate data point
								  {
									  LOG("ice", errs() << "Duplicated negative points should be impossible.\n");
									  exit (-3);
								  }
							  }
						  }
					  }
				  }

				  if (upd) {
					  // Ask machine learning for a new invariant for body_app.
					  // Expr pre = m_candidate_model.getDef(body_app);
					  //if (SVMExecPath.compare("") == 0)
						  C5learn (changedPreds);
					  //else
					  //	  svmLearn (changedPreds);
				  }
			  } while (upd);
			  }
			  // --- Extend worklist as we just go through a strengthening loop ----
			  if (counter > 1) {
				  if (posUpd) addUsedToWorkList (db, workList, r);
				  else addNewToWorkList (db, workList, r);
			  }
		  }
	  }
	  LOG("ice", errs() << "==================================================================\n";);
	  return true;
  }

  // Sample Horn Constraint System.
  // Fixme. Not suitable for non-linear Horn Constraint System.
  bool ICE::sampleLinearHornCtrs (Expr head, DataPoint p, int &index) {
	  std::map<Expr, ExprVector> relationToPositiveStateMap;
	  std::map<HornRule, int> transitionCount;
	  ExprVector equations;

	  for(int i=0; i<=bind::domainSz(head); i++) {
		  Expr var = bind::domainTy(head, i);
		  std::list<Expr>::iterator it = p.getAttrValues().begin();
		  std::advance(it, i);
		  Expr value = *it;

		  Expr arg_i_type = bind::domainTy(bind::fname (head), i);
		  std::ostringstream oss;
		  oss << *arg_i_type;

		  if (oss.str().compare("BOOL") == 0) {
			  oss.str(""); oss.clear(); oss << *value;
			  if (oss.str().compare("1") == 0) {
				  value = mk<TRUE>(var->efac());
			  } else if (oss.str().compare("0") == 0){
				  value = mk<FALSE>(var->efac());
			  } else {
				  exit (-3);
			  }
		  }

		  LOG("ice", errs() << "VAR: " << *var << "\n";);
		  LOG("ice", errs() << "VALUE: " << *value << "\n";);
		  equations.push_back(mk<EQ>(var, value));
	  }
	  Expr state_assignment;
	  if(equations.size() > 1)
		  state_assignment = mknary<AND>(equations.begin(), equations.end());
	  else
		  state_assignment = equations[0];
	  LOG("ice", errs() << "STATE ASSIGNMENT: " << *state_assignment << "\n";);

	  if(relationToPositiveStateMap.find(bind::fname(head)) == relationToPositiveStateMap.end()) {
		  ExprVector states;
		  states.push_back(state_assignment);
		  relationToPositiveStateMap.insert(std::make_pair(bind::fname(head), states));
	  } else {
		  ExprVector &states = relationToPositiveStateMap.find(bind::fname(head))->second;
		  states.push_back(state_assignment);
	  }

	  bool run = getReachableStates(transitionCount, relationToPositiveStateMap, head, p, index);
	  if (!run) return false;

	  LOG("ice", errs() << "THE WHOLE STATE MAP:\n";);
	  for(std::map<Expr, ExprVector>::iterator itr = relationToPositiveStateMap.begin(); itr != relationToPositiveStateMap.end(); ++itr) {
		  LOG("ice", errs() << "KEY: " << *(itr->first) << "\n";);
		  LOG("ice", errs() << "VALUE: [";);
		  for(ExprVector::iterator itr2 = itr->second.begin(); itr2 != itr->second.end(); ++itr2)
			  LOG("ice", errs() << *(*itr2) << ", ";);
		  LOG("ice", errs() << "]\n";);
	  }
	  return true;
  }

  // Sample Horn Constraint System.
  // Fixme. Not suitable for non-linear Horn Constraint System.
  bool ICE::getReachableStates(std::map<HornRule, int> &transitionCount, std::map<Expr, ExprVector> &relationToPositiveStateMap,
		  	  	  	  Expr from_pred, DataPoint p, int &index)
  {
	  auto &db = m_hm.getHornClauseDB();
	  for(HornClauseDB::RuleVector::iterator itr = db.getRules().begin(); itr != db.getRules().end(); ++itr)
	  {
		  HornRule r = *itr;
		  std::map<HornRule, int>::iterator itc = transitionCount.find(r);
		  if (itc != transitionCount.end() && itc->second >= RuleSampleLen) {
			  // Avoid infinitely unroll a rule!
			  // Fixme. Set maximum unrolling number to be 101 or ...
			  continue;
		  }

		  ExprVector body_preds;
		  get_all_pred_apps(r.body(), db, std::back_inserter(body_preds));

		  if(body_preds.size() == 1 && bind::fname(body_preds[0]) == bind::fname(from_pred))
		  {
			  ExprVector equations;
			  for(int i=0; i<=bind::domainSz(body_preds[0]); i++)
			  {
				  Expr var = bind::domainTy(body_preds[0], i);
				  std::list<Expr>::iterator it = p.getAttrValues().begin();
				  std::advance(it, i);
				  Expr value = *it;

				  Expr arg_i_type = bind::domainTy(bind::fname (body_preds[0]), i);
				  std::ostringstream oss;
				  oss << *arg_i_type;

				  if (oss.str().compare("BOOL") == 0) {
					  oss.str(""); oss.clear(); oss << *value;
					  if (oss.str().compare("1") == 0) {
						  value = mk<TRUE>(var->efac());
					  } else if (oss.str().compare("0") == 0){
						  value = mk<FALSE>(var->efac());
					  } else {
						  exit (-3);
					  }
				  }

				  LOG("ice", errs() << "VAR: " << *var << "\n";);
				  LOG("ice", errs() << "VALUE: " << *value << "\n";);
				  equations.push_back(mk<EQ>(var, value));
			  }
			  Expr state_assignment;
			  if(equations.size() > 1)
			  {
				  state_assignment = mknary<AND>(equations.begin(), equations.end());
			  }
			  else
			  {
				  state_assignment = equations[0];
			  }

			  bool run = getRuleHeadState(transitionCount, relationToPositiveStateMap, r, state_assignment, m_pos_index_map[p], index);
			  if (!run) return false;
		  }
	  }
	  return true;
  }


  // Sample Horn Constraint System.
  // Fixme. Not suitable for non-linear Horn Constraint System.
  bool ICE::getRuleHeadState(std::map<HornRule, int> &transitionCount, std::map<Expr, ExprVector> &relationToPositiveStateMap,
		  	  	  HornRule r, Expr from_pred_state, int pindex, int &index)
  {
	  LOG("ice", errs() << "RULE HEAD: " << *(r.head()) << "\n";);
	  LOG("ice", errs() << "RULE BODY: " << *(r.body()) << "\n";);

	  auto &db = m_hm.getHornClauseDB();
	  ZSolver<EZ3> solver(m_hm.getZContext());

	  solver.assertExpr(from_pred_state);
	  solver.assertExpr(extractTransitionRelation(r, db));
	  //solver.toSmtLib(outs());

	  int iteri = 0;
	  boost::tribool isSat = solver.solve();
	  while(isSat)
	  {
		  if(bind::domainSz(bind::fname(r.head())) == 0)
		  {
			  //Fixme. reach a predicate with empty signature.
			  outs()<<"Program is buggy.\n";
			  std::list<Expr> attr_values;
			  DataPoint pos_dp(bind::fname(bind::fname(r.head())), attr_values);
			  addPosCex(pos_dp);
			  failurePoint = m_pos_list.size()-1;
			  std::list<int> preIndices;
			  preIndices.push_back(pindex);
			  postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));
			  return false;
		  }

		  ZModel<EZ3> model = solver.getModel();
		  ExprVector equations;
		  std::list<Expr> attr_values;
		  ExprVector abstractEquations; // Do not assgin concrete values to uncertainties.
		  for(int i=0; i<=bind::domainSz(r.head()); i++)
		  {
			  Expr var = bind::domainTy(r.head(), i);
			  Expr value = model.eval(var);

			  if(bind::isBoolConst(value))
			  {
				  Expr uncertain_value = mk<FALSE>(value->efac());
				  value = uncertain_value;
			  }
			  else if(bind::isIntConst(value))
			  {
				  Expr uncertain_value = mkTerm<mpz_class>(0, value->efac());
				  value = uncertain_value;
			  } else
			  {
				  abstractEquations.push_back(mk<NEQ>(var, value));
			  }

			  LOG("ice", errs() << "VAR: " << *var << "\n";);
			  LOG("ice", errs() << "VALUE: " << *value << "\n";);
			  equations.push_back(mk<EQ>(var, value));

			  //convert true/false to 1/0 in C5 data point
			  if(isOpX<TRUE>(value))
			  {
				  value = mkTerm<mpz_class>(1, value->efac());
			  }
			  else if(isOpX<FALSE>(value))
			  {
				  value = mkTerm<mpz_class>(0, value->efac());
			  }
			  attr_values.push_back(value);
		  }
		  Expr state_assignment;
		  if(equations.size() > 1)
		  {
			  state_assignment = mknary<AND>(equations.begin(), equations.end());
		  }
		  else
		  {
			  state_assignment = equations[0];
		  }
		  LOG("ice", errs() << "STATE ASSIGNMENT: " << *state_assignment << "\n";);

		  DataPoint pos_dp(bind::fname(bind::fname(r.head())), attr_values);
		  int orig_size = m_pos_data_set.size();
		  addPosCex(pos_dp);

		  if(m_pos_data_set.size() == orig_size + 1) //no duplicate
		  {
			  Expr r_head = r.head();
			  if (!ICEICE) {
			  m_cex_list.erase(std::remove_if(m_cex_list.begin(), m_cex_list.end(),
					  [pos_dp,r_head,this](DataPoint p) {
			  	  return p.getPredName() == bind::fname(bind::fname(r_head))
			  	  	  	  	  && m_neg_data_set.find(p) != m_neg_data_set.end();
			  }), m_cex_list.end());


			  for (std::set<DataPoint>::iterator it = m_neg_data_set.begin(); it != m_neg_data_set.end(); ) {
				  if (it->getPredName() == bind::fname(bind::fname(r_head))) {
					  //if (*it == pos_dp) {
					  m_neg_data_set.erase (it++);
				  } else {
					  ++it;
				  }
			  }
			  m_neg_data_count.erase (pos_dp.getPredName());
			  }
			  m_cex_list.push_back(pos_dp);
			  addDataPointToIndex(pos_dp, index);

			  std::list<int> preIndices;
			  preIndices.push_back(pindex);
			  postree.insert(std::make_pair (m_pos_list.size()-1, preIndices));

			  LOG("ice", errs() << "POS CEX, INDEX IS " << index << "\n";);
			  index++;

			  ExprVector arg_list;
			  Expr rel = bind::fname (r_head);
			  for(int i=0; i<bind::domainSz(rel); i++)
			  {
				  Expr arg_i_type = bind::domainTy(rel, i);
				  Expr arg_i = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
				  arg_list.push_back(arg_i);
			  }
			  Expr fapp = bind::fapp(rel, arg_list);
			  Expr True = mk<TRUE>(rel->efac());
			  m_candidate_model.addDef(fapp, True);

			  if(relationToPositiveStateMap.find(bind::fname(r.head())) == relationToPositiveStateMap.end())
			  {
				  ExprVector states;
				  states.push_back(state_assignment);
				  relationToPositiveStateMap.insert(std::make_pair(bind::fname(r.head()), states));
			  }
			  else
			  {
				  ExprVector &states = relationToPositiveStateMap.find(bind::fname(r.head()))->second;
				  states.push_back(state_assignment);
			  }

			  std::map<HornRule, int>::iterator itc = transitionCount.find(r);
			  if (itc == transitionCount.end()) {
				  transitionCount.insert(std::make_pair(r, 1));
			  } else {
				  itc->second = itc->second + 1;
			  }

			  bool run = getReachableStates(transitionCount, relationToPositiveStateMap, r.head(), pos_dp, index);
			  if (!run) return false;

			  itc = transitionCount.find(r);
			  itc->second = itc->second - 1;
		  }

		  // Iterate with the next possible solution.
		  iteri ++;
		  if (iteri >= RuleSampleWidth) {
			  // Enough samples ?
			  break;
		  }

		  Expr notagain;
		  if(abstractEquations.size() > 1)
		  {
			  notagain = mknary<OR>(abstractEquations.begin(), abstractEquations.end());
		  } else if (abstractEquations.size() == 1) {
			  notagain = abstractEquations[0];
		  } else {
			  // There is nothing to be re-sampled ?
			  break;
		  }

		  solver.assertExpr(notagain);
		  isSat = solver.solve();
	  }
	  return true;
  }

  // ICE: Induction CounterExample guided invariant inference.
  void ICE::runICE()
  {
	  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  	  //load the Horn clause database
  	  auto &db = m_hm.getHornClauseDB ();
  	  db.buildIndexes ();
  	  LOG("ice", errs() << "DB: \n" << cyan << db << normal;);
			errs() << "===========================================================\n";
			for (auto& rel : db.m_rels)
				LOG("ice", errs() << "db relation: " << cyan << bold << *rel << normal << "\n");
			errs() << "===========================================================\n";

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
  		  if (!no_verification_found_error) { // A buggy program is catched.
  			  break;
  		  } 
  		  c ++;
  	  }

  	  std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
  	  outs() << "************** CHCs Solved in " <<
  			  (std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count()) /1000000.0 << " (secs) **************\n\n";
  }
}
