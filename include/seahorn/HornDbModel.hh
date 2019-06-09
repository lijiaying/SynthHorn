#ifndef HORNDBMODEL__HH_
#define HORNDBMODEL__HH_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  class HornDbModel
  {
  private:
    ExprMap m_defs;
  public:
    HornDbModel() {}
    void addDef(Expr fapp, Expr lemma);
    Expr getDef(Expr fapp);
    bool hasDef (Expr fdecl);
    virtual ~HornDbModel() {}
    void Print (llvm::raw_ostream &os) const
    {
      for (auto def: m_defs)
        os << *def.first << "   =>=>=>  " << *def.second << "\n";
    }

  };

  /// Extract HornDbModel of a given horn db from a ZFixedPoint. 
  void initDBModelFromFP(HornDbModel &dbModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp);

  inline llvm::raw_ostream & operator<< (llvm::raw_ostream &os, const HornDbModel& model)
  {
    model.Print(os);
    return os;
  }
}

#endif
