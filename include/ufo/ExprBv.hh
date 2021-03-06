#ifndef __EXPR_BV__HH_
#define __EXPR_BV__HH_

#include <boost/core/demangle.hpp>

// #include "color.hh"
#define thered "\e[31m"
#define thegreen "\e[32m"
#define theyellow "\e[33m"
#define theblue "\e[34m"
#define themag "\e[35m"
#define thecyan "\e[36m"
#define thegray "\e[37m"

#define thenormal "\e[0m"
#define thebold "\e[1m"
#define theunderline "\e[4m"


#define TYPE(X) boost::core::demangle(typeid(X).name())

/** Bit-Vector expressions 

 * This file is included from middle of Expr.hpp
 */
namespace expr
{
	namespace op
	{
		namespace bv
		{
			struct BvSort
			{
				unsigned m_width;
				BvSort (unsigned width) : m_width (width) {}
				BvSort (const BvSort &o) : m_width (o.m_width) {}

				bool operator< (const BvSort &b) const { return m_width < b.m_width; }
				bool operator== (const BvSort &b) const { return m_width == b.m_width; }
				bool operator!= (const BvSort &b) const { return m_width != b.m_width; }

				size_t hash () const
				{
					std::hash<unsigned> hasher;
					return hasher (m_width);
				}

				void Print (std::ostream &OS) const { OS << "bv(" << m_width << ")"; }	
			};

			inline std::ostream &operator<< (std::ostream &OS, const BvSort &b)
			{
				b.Print (OS);
				return OS;
			}       
		}
	}

	template<> struct TerminalTrait<const op::bv::BvSort>
	{
		// typedef const op::bv::BvSort value_type;

		static inline void print (std::ostream &OS, const op::bv::BvSort &b, int depth, bool brkt) 
		{ OS << b; }

		static inline bool less (const op::bv::BvSort &b1, const op::bv::BvSort &b2)
		{ return b1 < b2; }

		static inline bool equal_to (const op::bv::BvSort &b1, const op::bv::BvSort &b2)
		{ return b1 == b2; }

		static inline size_t hash (const op::bv::BvSort &b) 
		{ return b.hash (); }
	};

	namespace op
	{
		typedef Terminal<const bv::BvSort> BVSORT;

		namespace bv
		{
			inline Expr bvsort (unsigned width, ExprFactory &efac)
			{return mkTerm<const BvSort> (BvSort (width), efac);}

			inline unsigned width (Expr bvsort)
			{return getTerm<const BvSort>(bvsort).m_width;}

			/// Bit-vector numeral of a given sort
			/// num is an integer numeral, and bvsort is a bit-vector sort
			inline Expr bvnum (Expr num, Expr bvsort)
			{return bind::bind (num, bvsort);}

			/// bit-vector numeral of an arbitrary precision integer
			inline Expr bvnum (mpz_class num, unsigned bwidth, ExprFactory &efac)
			{return bvnum (mkTerm (num, efac), bvsort (bwidth, efac));}

			/// true if v is a bit-vector numeral
			inline bool is_bvnum (Expr v)
			{
				return isOpX<BIND> (v) && v->arity () == 2 &&
					isOpX<MPZ> (v->arg (0)) && isOpX<BVSORT> (v->arg (1));
			}

			inline mpz_class toMpz (Expr v)
			{
				assert (is_bvnum (v));
				return getTerm<mpz_class> (v->arg (0));
			}

			inline Expr bvConst (Expr v, unsigned width)
			{
				Expr sort = bvsort (width, v->efac ());
				return bind::mkConst (v, sort);
			}

		}

		NOP_BASE(BvOp)
			NOP(BNOT,"bvnot",FUNCTIONAL,BvOp)
			NOP(BREDAND,"bvredand",FUNCTIONAL,BvOp)
			NOP(BREDOR,"bvredor",FUNCTIONAL,BvOp)
			NOP(BAND,"bvand",FUNCTIONAL,BvOp)
			NOP(BOR,"bvor",FUNCTIONAL,BvOp)
			NOP(BXOR,"bvxor",FUNCTIONAL,BvOp)
			NOP(BNAND,"bvnand",FUNCTIONAL,BvOp)
			NOP(BNOR,"bvnor",FUNCTIONAL,BvOp)
			NOP(BXNOR,"bvxnor",FUNCTIONAL,BvOp)
			NOP(BNEG,"bvneg",FUNCTIONAL,BvOp)
			NOP(BADD,"bvadd",FUNCTIONAL,BvOp)
			NOP(BSUB,"bvsub",FUNCTIONAL,BvOp)
			NOP(BMUL,"bvmul",FUNCTIONAL,BvOp)
			NOP(BUDIV,"bvudiv",FUNCTIONAL,BvOp)
			NOP(BSDIV,"bvsdiv",FUNCTIONAL,BvOp)
			NOP(BUREM,"bvurem",FUNCTIONAL,BvOp)
			NOP(BSREM,"bvsrem",FUNCTIONAL,BvOp)
			NOP(BSMOD,"bvsmod",FUNCTIONAL,BvOp)
			NOP(BULT,"bvult",FUNCTIONAL,BvOp)
			NOP(BSLT,"bvslt",FUNCTIONAL,BvOp)
			NOP(BULE,"bvule",FUNCTIONAL,BvOp)
			NOP(BSLE,"bvsle",FUNCTIONAL,BvOp)
			NOP(BUGE,"bvuge",FUNCTIONAL,BvOp)
			NOP(BSGE,"bvsge",FUNCTIONAL,BvOp)
			NOP(BUGT,"bvugt",FUNCTIONAL,BvOp)
			NOP(BSGT,"bvsgt",FUNCTIONAL,BvOp)
			NOP(BCONCAT,"concat",FUNCTIONAL,BvOp)
			NOP(BEXTRACT,"extract",FUNCTIONAL,BvOp)
			NOP(BSEXT,"bvsext",FUNCTIONAL,BvOp)
			NOP(BZEXT,"bvzext",FUNCTIONAL,BvOp)
			NOP(BREPEAT,"bvrepeat",FUNCTIONAL,BvOp)
			NOP(BSHL,"bvshl",FUNCTIONAL,BvOp)
			NOP(BLSHR,"bvlshr",FUNCTIONAL,BvOp)
			NOP(BASHR,"bvashr",FUNCTIONAL,BvOp)
			NOP(BROTATE_LEFT,"bvrotleft",FUNCTIONAL,BvOp)
			NOP(BROTATE_RIGHT,"bvrotright",FUNCTIONAL,BvOp)
			NOP(BEXT_ROTATE_LEFT,"bvextrotleft",FUNCTIONAL,BvOp)
			NOP(BEXT_ROTATE_RIGHT,"bvextrotright",FUNCTIONAL,BvOp)
			NOP(INT2BV,"int2bv",FUNCTIONAL,BvOp)
			NOP(BV2INT,"bv2int",FUNCTIONAL,BvOp)

			namespace bv
			{
				/* XXX Add helper methods as needed */

				inline Expr bvnot (Expr v) {return mk<BNOT> (v);}

				inline Expr extract (unsigned high, unsigned low, Expr v)
				{
					assert (high > low);
					return mk<BEXTRACT> (mkTerm<unsigned> (high, v->efac ()), 
							mkTerm<unsigned> (low, v->efac ()), v);
				}

				/// high bit to extract
				inline unsigned high (Expr v) {return getTerm<unsigned> (v->arg (0));}
				/// low bit to extract
				inline unsigned low (Expr v) {return getTerm<unsigned> (v->arg (1));}
				/// bv argument to extract
				inline Expr earg (Expr v) {return v->arg (2);}

				inline Expr sext (Expr v, unsigned width)
				{return mk<BSEXT> (v, bvsort (width, v->efac ()));}

				inline Expr zext (Expr v, unsigned width) 
				{return mk<BZEXT> (v, bvsort (width, v->efac ()));}

			}

		namespace bind{
			inline Expr bvVar (unsigned width, Expr name)
			{ return var (name, mkTerm<const bv::BvSort>(bv::BvSort(width), name->efac ())); }

			inline Expr bvConstDecl (unsigned width, Expr name)
			{ return constDecl (name, mkTerm<const bv::BvSort>(bv::BvSort(width), name->efac ())); }

			inline Expr bvConst (unsigned width, Expr name) { return fapp (bvConstDecl (width, name)); }
			inline bool isBvConst (Expr v) { return isConst<BVSORT> (v); }

			inline bool isBvVar (Expr v) { return isVar<BVSORT>(v); }

			inline unsigned getWidth(Expr v) {
				return 32;
				// std::cout << thebold << thered << " getWidth: {" << *v << "} type: " << TYPE(*v) << " ------------------\n" << thenormal;
				Expr s = v;
				if (isBvConst(v)) {
					// std::cout << thered << "   is Bv Const\n" << thenormal;
					s = bind::type(fname(v));
					// std::cout << thered << "   s = bind::type(fname(v)): " << s << " type:" << TYPE(s) << "\n" << thenormal;
				}
				assert (isOpX<BVSORT>(s));
				/*
				if (isOpX<BVSORT>(s) == false)
					std::cout << thered << "   s: " << s << " is not BVSORT\n" << thenormal;
				else
					std::cout << thered << "   s: " << s << " is in BVSORT\n" << thenormal;
				*/
				return getTerm<const bv::BvSort>(s).m_width;
			}


			inline Expr typeOf (Expr v)
			{
				// std::cout << "------ checking type of " << *v << " ---------\n";
				using namespace bind;
				if (isOpX<VARIANT> (v)) return typeOf (variant::mainVariant (v));
				if (isOpX<FAPP> (v))
				{
					assert (isOpX<FDECL> (v->left ()));
					return rangeTy (v->left ());
				}
				if (isOpX<TRUE> (v) || isOpX<FALSE> (v)) return mk<BOOL_TY> (v->efac ());
				if (isOpX<MPZ> (v)) return mk<INT_TY> (v->efac ());
				if (isOpX<MPQ> (v)) return mk<REAL_TY> (v->efac ());
				if (isOpX<BIND> (v)) return bind::type (v);
				if (isBoolVar (v) || isBoolConst (v)) return mk<BOOL_TY> (v->efac ());
				if (isIntVar (v) || isIntConst (v)) return mk<INT_TY> (v->efac ());
				if (isBvVar (v) || isBvConst (v)) {
					// std::cout << "###################### isBvvar or isBvConst\n";
					int width = getWidth(v);
					// std::cout << "###################### after get width\n";
					return mkTerm<const bv::BvSort> (bv::BvSort(width), v->efac ());
					// return mkTerm<const bv::BvSort> (getTerm<const bv::BvSort>(v->arg(1)).m_width, v->efac ());
				}
				if (isRealVar (v) || isRealConst (v)) return mk<REAL_TY> (v->efac ());
				std::cerr << "WARNING: could not infer type of: " << *v << "\n";

				assert (0 && "Unreachable");
				return Expr();    
			}
			inline Expr sortOf (Expr v) {return typeOf (v);}

			/*
			inline void checkIsBv(Expr v) {
				std::cout << theblue << "********************* check is bv **************************\n" << thenormal;
				std::cout << thegreen << " $$ check is BvNum of Expr: " << *v << "  typeid: " << TYPE(*v) << "\n" << thenormal;
				if (isBvVar(v)) std::cout << "    |-- is BvVar.\n";
				else if (isBvConst(v)) std::cout << "    |-- is BvConst.\n";
				else if (bv::is_bvnum(v)) std::cout << "    |-- is Bvnum.\n";
				else std::cout << "    |-- is NOT BvVar/BvConst/BvNum.\n";
				std::cout << theblue << "****************** ret ************************\n" << thenormal;
			}
			*/

			/*
			inline void outputTypeStr(Expr v)
			{
				using namespace bind;
				std::cout << thebold << thecyan <<  "** getTypeStr for v-> " << *v << "\n" << thenormal;

				if (isOpX<FAPP> (v)) {
					std::cout << thebold << theblue << " fapp: {" << *v << "} ------------------\n" << thenormal;
					Expr fdecl = fname(v);
					std::cout << theyellow << "   |-fdecl: {" << *fdecl << "}\n" << thenormal;
					for (int i = 0; i < v->arity(); i++)
						std::cout << theyellow << "   |- args[" << i << "] = {" << *(v->arg(i)) << "}\n" << thenormal;
					std::cout << thebold << theblue << " fapp done: {" << *v << "} ------------------\n" << thenormal;
				} else {
					std::cout << thebold << theblue << " Expr(not fapp): {" << *v << "} ------------------\n" << thenormal;
					for (int i = 0; i < v->arity(); i++) {
						std::cout << theyellow << "       |- args[" << i << "] = {" << *(v->arg(i)) << "}\n" << thenormal;
					}
					std::cout << thebold << theblue << " Expr done: {" << *v << "} ------------------\n" << thenormal;
				}

				if (isOpX<VARIANT> (v)) 
					std::cout << "1: " << *typeOf (variant::mainVariant (v));
				else if (isOpX<BIND> (v))
					std::cout << "2. is OpX<BIND>\n";
				else if (isBvVar (v) || isBvConst (v)) 
				{
					std::cout << "###################### isBvvar or isBvConst\n";
					unsigned width = getWidth(v);
					std::cout << "###################### after get width\n";
					std::cout << "3: bv " << *mkTerm<const bv::BvSort> (bv::BvSort(width), v->efac ());
				}	
				else if (isOpX<TRUE> (v) || isOpX<FALSE> (v)) 
					std::cout << "4: true/false " << *mk<BOOL_TY> (v->efac ());
				else if (isOpX<MPZ> (v)) 
					std::cout << "5: int " << *mk<INT_TY> (v->efac ());
				else if (isOpX<MPQ> (v)) 
					std::cout << "7: mpq " << *mk<REAL_TY> (v->efac ());
				else if (isBoolVar (v) || isBoolConst (v)) 
					std::cout << "8: bool " << *mk<BOOL_TY> (v->efac ());
				else if (isIntVar (v) || isIntConst (v)) 
					std::cout << "9: int " << *mk<INT_TY> (v->efac ());
				else if (isRealVar (v) || isRealConst (v)) 
					std::cout << "10: " << *mk<REAL_TY> (v->efac ());
				else 
					std::cout << " xx NOT match xx \n"; 
				std::cout << " ================================================ \n"; 
				return;
			}
			*/

		}

	}
}


#endif /*  __EXPR_BV__HH_ */
