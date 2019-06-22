#ifndef ICE__HH_
#define ICE__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/GuessCandidates.hh"
#include "seahorn/HornDbModel.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>

#include <algorithm>

namespace seahorn
{
	using namespace llvm;

	class ICEPass : public llvm::ModulePass
	{
		public:
			static char ID;

			ICEPass() : ModulePass(ID) {}
			virtual ~ICEPass() {}

			virtual bool runOnModule (Module &M);
			virtual void getAnalysisUsage (AnalysisUsage &AU) const;
			virtual const char* getPassName () const {return "ICE";}
	};

	class DataPoint
	{
		Expr m_pred;
		std::list<Expr> m_values;
		public:
		DataPoint() {}
		DataPoint(Expr pred, std::list<Expr>& attr_values) : m_pred(pred), m_values(attr_values) {}
		virtual ~DataPoint() {}
		Expr getPredName() const {return m_pred;}
		std::list<Expr>& getAttrValues() {return m_values;}

		size_t hash () const
		{
			size_t res = expr::hash_value (m_pred);
			boost::hash_combine (res, boost::hash_range (m_values.begin (),
						m_values.end ()));
			return res;
		}

		bool operator==(const DataPoint & other) const
		{ return hash() == other.hash ();}

		bool operator<(const DataPoint & other) const
		{ return hash() < other.hash ();}
	};

	class ICE
	{
		public:
			ICE(HornifyModule &hm) : m_hm(hm)  {failurePoint = -1; n_svm_calls = 0;}
			virtual ~ICE() {/*m_fp.reset (nullptr);*/}
		private:
			HornifyModule &m_hm;
			HornDbModel m_candidate_model;

			std::string m_C5filename;

			ExprMap m_attr_name_to_expr_map;
			ExprMap m_rel_to_c5_rel_name_map;
			ExprMap m_c5_rel_name_to_rel_map;

			ExprMap m_svmattr_name_to_expr_map;
			std::map<Expr, std::string> m_svmattr_name_to_str_map;

			// Set a fixed number of predicates used for ICE (boolean) learning.
			ExprMap m_pred_name_to_expr_map;

			// Collect integers in the rules ...
			// Fixme. It seems we only need to consider mod operations.
			std::set<int> ruleConstants;

			// Colect unknownes in the rules
			std::map<Expr, std::vector<bool>> unknowns;

			std::set<DataPoint> m_pos_data_set;
			std::set<DataPoint> m_neg_data_set;
			//std::set<DataPoint> m_impl_data_set;
			std::set<DataPoint> m_impl_cex_set;
			std::set<std::pair<DataPoint, DataPoint>> m_impl_pair_set;

			//std::set<DataPoint> m_potential_pos_data_set;
			//std::set<DataPoint> m_potential_neg_data_set;

			std::map<DataPoint, int> m_data_point_to_index_map;
			std::vector<DataPoint> m_cex_list;

			std::map<Expr, int> m_neg_data_count;
			std::map<Expr, int> m_pos_data_count;
			std::map<Expr, int> m_impl_data_count;

			std::map<DataPoint, int> m_pos_index_map;
			std::vector<DataPoint> m_pos_list;
			std::map<int, std::list<int>> postree;
			int failurePoint;

			int n_svm_calls;

			boost::tribool m_z3_sat;
			std::map<std::string, std::pair<std::string, std::string>> m_z3_model; // var_name: <var_type, var_value>
			// std::list<Expr> m_model; // var_name: <var_type, var_value>
			std::map<std::string, Expr> m_model;
			std::string m_z3_model_str;
		public:
			void setupC5();
			void initC5(ExprVector targets);
			void C5learn(ExprVector targets);
			std::string DataPointToStr(ExprVector targets, DataPoint p, bool valueOnly = false);
			// bool callExternalZ3ToSolve(std::string smt2str);
			boost::tribool callExternalZ3ToSolve(ZSolver<EZ3> solver);
			bool parseModelFromString(std::string model_str);

		public:
			HornifyModule& getHornifyModule() {return m_hm;}
			HornDbModel& getCandidateModel() {return m_candidate_model;}

			//std::set<HornRule>& getPosRuleSet() {return m_pos_rule_set;}
			//std::set<HornRule>& getNegRuleSet() {return m_neg_rule_set;}

		public:
			void runICE();

			void guessCandidates(HornClauseDB &db);

			//Add ICE invs to default solver
			void addInvarCandsToProgramSolver();

			void genInitialCandidates(HornClauseDB &db);
			void generateC5DataAndImplicationFiles(ExprVector targets);

			//void constructPosAndNegRules(HornClauseDB &db);

			void addPosCex(DataPoint dp) {
				m_pos_data_set.insert(dp);
				std::map<Expr, int>::iterator it = m_pos_data_count.find(dp.getPredName());
				if (it != m_pos_data_count.end())
					it->second ++;
				else
					m_pos_data_count.insert (std::make_pair(dp.getPredName(), 1));

				m_pos_list.push_back (dp);
				m_pos_index_map.insert (std::make_pair(dp, m_pos_list.size()-1));
			}

			void addNegCex(DataPoint dp) {
				m_neg_data_set.insert(dp);
				std::map<Expr, int>::iterator it = m_neg_data_count.find(dp.getPredName());
				if (it != m_neg_data_count.end())
					it->second ++;
				else
					m_neg_data_count.insert (std::make_pair(dp.getPredName(), 1));
			}

			//      void addImplCex(DataPoint dp) {
			//    	  m_impl_data_set.insert(dp);
			//		  std::map<Expr, int>::iterator it = m_impl_data_count.find(dp.getPredName());
			//		  if (it != m_impl_data_count.end())
			//			  it->second ++;
			//		  else
			//			  m_impl_data_count.insert (std::make_pair(dp.getPredName(), 1));
			//      }

			void drawDataPoint(DataPoint& dp, std::string ending = "") {
				Expr pred_cname = dp.getPredName();
				outs() << *pred_cname << "(";
				int i = 0;
				for(Expr attr :  dp.getAttrValues()) {
					if (i < dp.getAttrValues().size() - 1)
						outs() << *attr << ",";
					else
						outs() << *attr;
					i++;
				}
				outs() << ")" << ending;
			}

			void drawPosTree (int pindex) {
				DataPoint p = m_pos_list[pindex];
				if (postree.find(pindex) != postree.end()) 
				{
					if (postree[pindex].size() > 0) 
					{
						for (int index : postree[pindex]) {
							drawPosTree (index);
							// Draw the reach-to relation.  PRE --> P
							DataPoint pre = m_pos_list[index];
							drawDataPoint(pre, "  -->  ");
							drawDataPoint(p, "\n");
						} // end for
					} 
					else 
					{ // Fact --> P
						outs() << "Fact  -->  ";
						drawDataPoint(p, "\n");
					} 
				}
				else 
				{ // Entry --> P
					outs() << "Entry  -->  ";
					drawDataPoint(p, "\n");
				}
			}

			void drawPosTree () {
				if (failurePoint >= 0 && failurePoint < m_pos_list.size())
					drawPosTree (failurePoint);
			}

			void addImplCex(DataPoint dp) {m_impl_cex_set.insert(dp);}
			void addImplPair(std::pair<DataPoint, DataPoint> pair) {m_impl_pair_set.insert(pair);}

			void addDataPointToIndex(DataPoint dp, int index) {m_data_point_to_index_map.insert(std::make_pair(dp, index));}

			void convertPtreeToInvCandidate(boost::property_tree::ptree pt, ExprVector targets);
			std::list<std::list<Expr>> constructFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt);
			// std::list<std::list<Expr>> constructBoundedFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt);
			// std::list<std::list<Expr>> constructUnboundedFormula(std::list<Expr> stack, boost::property_tree::ptree sub_pt);

			//ZFixedPoint<EZ3>& resetFixedPoint(HornClauseDB &db);

			//void setPosQuery();

			//void recordPosCexs(HornClauseDB &db, bool &isChanged, int &index);
			//bool recordNegCexs(HornClauseDB &db, bool &isChanged, int &index);
			//void recordImplPairs(HornClauseDB &db, bool &isChanged, int &index);

			Expr plusAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name);
			Expr minusAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name);
			Expr modAttrToDecisionExpr(boost::property_tree::ptree sub_pt, std::string attr_name);

			void saveInvsToSmtLibFile();

			void invalidateQueries(HornClauseDB &db);
			Expr extractRelation (HornRule r, HornClauseDB &db, Expr t, Expr s);
			bool solveConstraints(HornClauseDB &db, bool &isChanged, int &index);
			void fastSolveConstraints(HornClauseDB &db, bool &isChanged, int &index);
			bool generatePostiveSamples (HornClauseDB &db, HornRule r, ZSolver<EZ3> solver, int& index, bool& run);
			bool fastGeneratePostiveSamples (HornClauseDB &db, HornRule r, ZSolver<EZ3> solver, int& index);
			int countSamples (Expr pred, bool positive);
			bool matchFacts (HornClauseDB &db, DataPoint p);
			void extractFacts (HornClauseDB &db, ExprVector targets);
			void clearNegSamples (Expr app, bool b);

			// Sample Horn Constraint System.
			// Fixme. Not suitable for non-linear Horn Constraint System.
			bool getReachableStates(std::map<HornRule, int> &transitionCount, std::map<Expr, ExprVector> &relationToPositiveStateMap,
					Expr from_pred, DataPoint p, int &index);
			bool getRuleHeadState(std::map<HornRule, int> &transitionCount, std::map<Expr, ExprVector> &relationToPositiveStateMap,
					HornRule r, Expr from_pred_state, int pindex, int &index);
			bool sampleLinearHornCtrs(Expr pred, DataPoint p, int &index);
			void svmLearn (Expr targetName); //(ExprVector target);
			void extractConstants(HornClauseDB &db);
			void extractUnknowns(HornClauseDB &db);

			void outputDataSetInfo();
	};
}

#endif /* ICE__HH_ */
