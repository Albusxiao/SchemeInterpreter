/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>
#include <list>
#include <bits/stl_algo.h>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) {
    // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) {
    // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) {
    // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) {
    // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) {
    // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) {
    // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) {
    // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) {
    // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) {
    // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) {
    // evaluation of multi-operator primitive
    // TODO: TO COMPLETE THE VARIADIC CLASS
    std::vector<Value> temp;
    temp.clear();
    for (Expr i: rands)temp.push_back(i->eval(e));
    return evalRator(temp);
}

bool try_parse_as_number(const std::string &st) {
    if ((st[0] == '+' || st[0] == '-') && st.size() == 1)return false;
    for (int i = 0; i < st.size(); i++) {
        if (i == 0 && st[i] == '+' || st[i] == '-')continue;
        if (isdigit(st[i]))continue;
        return false;
    }
    return true;
}

Value Var::eval(Assoc &e) {
    // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    if (x.empty()) throw(RuntimeError("Invalid variable name"));
    if (x[0] == '.' || x[0] == '@') throw(RuntimeError("Invalid variable name"));
    // First-character cannot be a digit
    if (isdigit(static_cast<unsigned char>(x[0]))) throw(RuntimeError("Invalid variable name"));

    // If the token as a whole can be parsed as a number, treat it as a number.
    if (try_parse_as_number(x)) {
        bool neg = false;
        int n = 0;
        int i = 0;
        if (x[0] == '-') {
            i += 1;
            neg = true;
        } else if (x[0] == '+') {
            i += 1;
        }
        for (; i < (int)x.size(); i++) {
            if (isdigit(x[i])) n = n * 10 + x[i] - '0';
        }
        return IntegerV(neg ? -n : n);
    }

    // Variable names must not contain these characters
    if (x.find('#') != std::string::npos || x.find('\'') != std::string::npos || x.find('"') != std::string::npos || x.find('`') != std::string::npos) {
        throw(RuntimeError("Invalid variable name"));
    }
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string> > > primitive_map = {
                {E_VOID, {new MakeVoid(), {}}},
                {E_EXIT, {new Exit(), {}}},
                {E_BOOLQ, {new IsBoolean(new Var("parm")), {"parm"}}},
                {E_INTQ, {new IsFixnum(new Var("parm")), {"parm"}}},
                {E_NULLQ, {new IsNull(new Var("parm")), {"parm"}}},
                {E_PAIRQ, {new IsPair(new Var("parm")), {"parm"}}},
                {E_PROCQ, {new IsProcedure(new Var("parm")), {"parm"}}},
                {E_SYMBOLQ, {new IsSymbol(new Var("parm")), {"parm"}}},
                {E_STRINGQ, {new IsString(new Var("parm")), {"parm"}}},
                {E_DISPLAY, {new Display(new Var("parm")), {"parm"}}},
                {E_PLUS, {new PlusVar({}), {}}},
                {E_MINUS, {new MinusVar({}), {}}},
                {E_MUL, {new MultVar({}), {}}},
                {E_DIV, {new DivVar({}), {}}},
                {E_MODULO, {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1", "parm2"}}},
                {E_EXPT, {new Expt(new Var("parm1"), new Var("parm2")), {"parm1", "parm2"}}},
                {E_EQQ, {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {
                //TODO
                return ProcedureV(it->second.second, it->second.first, e);
            }
        }
        if (reserved_words.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string> > > reserved_map = {
                {E_BEGIN, {new Begin({}), {}}},
                {E_QUOTE, {new Quote(new List), {}}},
                {E_IF, {new If(new Var("parm1"), new Var("parm2"), new Var("parm3")), {"parm1", "parm2", "parm3"}}},
                {E_COND, {new Cond({}), {}}},
                {E_LAMBDA, {new Lambda({}, new Var("parm")), {{}, "parm"}}},
                {E_DEFINE, {new Define({}, new Var("parm")), {{}, "parm"}}},
                {E_LET, {new Let({}, new Var("parm")), {{}, "parm"}}},
                {E_LETREC, {new Letrec({}, new Var("parm")), {{}, "parm"}}},
                {E_SET, {new Set({}, new Var("parm")), {{}, "parm"}}},
            };
            auto it = reserved_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != reserved_map.end()) {
                //TODO
                return ProcedureV(it->second.second, it->second.first, e);
            }
        }
    }
    return matched_value;
}
struct Rational_L {
    int denominator, numerator;
    Rational_L(int n, int d) :denominator(d),numerator(n){}
};
Value distribute(Rational_L &ans) {
    int temp = std::__gcd(ans.denominator, ans.numerator);
    ans.denominator /= temp;
    ans.numerator /= temp;
    if (ans.denominator < 0) {
        ans.denominator = -ans.denominator;
        ans.numerator = -ans.numerator;
    }
    if (ans.denominator == 0)throw(RuntimeError("Unknown Error"));
    if (ans.denominator == 1)return IntegerV(ans.numerator);
    else return RationalV(ans.numerator, ans.denominator);
}

bool IS_DIGIT(const Value &rand1) {
    return (rand1->v_type == V_INT || rand1->v_type == V_RATIONAL);
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) {
    // +
    //TODO: To complete the addition logic
    if (IS_DIGIT(rand1) && IS_DIGIT(rand2)) {
        Rational_L sum(1, 1);
        if (rand1->v_type == V_INT)sum.numerator = dynamic_cast<Integer *>(rand1.get())->n;
        else if (rand1->v_type == V_RATIONAL) {
            sum.numerator = dynamic_cast<Rational *>(rand1.get())->numerator;
            sum.denominator = dynamic_cast<Rational *>(rand1.get())->denominator;
        }
        if (rand2->v_type == V_INT)sum.numerator += dynamic_cast<Integer *>(rand2.get())->n * sum.denominator;
        else if (rand2->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(rand2.get())->numerator,
                             dynamic_cast<Rational *>(rand2.get())->denominator);
            int temp = std::__gcd(temp_RA.denominator, sum.denominator);
            temp = static_cast<int>(temp_RA.denominator) * sum.denominator / temp;
            sum.numerator *= temp / sum.denominator;
            sum.denominator = temp;
            sum.numerator += static_cast<int>(temp_RA.numerator) * temp / static_cast<int>(temp_RA.denominator);
        }
        return distribute(sum);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) {
    // -
    //TODO: To complete the substraction logic
    if (IS_DIGIT(rand1) && IS_DIGIT(rand2)) {
        Rational_L difference(1, 1);
        if (rand1->v_type == V_INT)difference.numerator = dynamic_cast<Integer *>(rand1.get())->n;
        else if (rand1->v_type == V_RATIONAL) {
            difference.numerator = dynamic_cast<Rational *>(rand1.get())->numerator;
            difference.denominator = dynamic_cast<Rational *>(rand1.get())->denominator;
        }
        if (rand2->v_type == V_INT)
            difference.numerator -= dynamic_cast<Integer *>(rand2.get())->n * difference.
                    denominator;
        else if (rand2->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(rand2.get())->numerator,
                             dynamic_cast<Rational *>(rand2.get())->denominator);
            int temp = std::__gcd(temp_RA.denominator, difference.denominator);
            temp = static_cast<int>(temp_RA.denominator) * difference.denominator / temp;
            difference.numerator *= temp / difference.denominator;
            difference.denominator = temp;
            difference.numerator -= static_cast<int>(temp_RA.numerator) * temp / static_cast<int>(temp_RA.denominator);
        }
        return distribute(difference);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) {
    // *
    //TODO: To complete the Multiplication logic
    if (IS_DIGIT(rand1) && IS_DIGIT(rand2)) {
        Rational_L multi(1, 1);
        if (rand1->v_type == V_INT)multi.numerator = dynamic_cast<Integer *>(rand1.get())->n;
        else if (rand1->v_type == V_RATIONAL) {
            multi.numerator = dynamic_cast<Rational *>(rand1.get())->numerator;
            multi.denominator = dynamic_cast<Rational *>(rand1.get())->denominator;
        }
        if (rand2->v_type == V_INT)multi.numerator *= dynamic_cast<Integer *>(rand2.get())->n;
        else if (rand2->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(rand2.get())->numerator,
                             dynamic_cast<Rational *>(rand2.get())->denominator);
            multi.numerator *= temp_RA.numerator;
            multi.denominator *= temp_RA.denominator;
        }
        return distribute(multi);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) {
    // /
    //TODO: To complete the dicision logic
    if (IS_DIGIT(rand1) && IS_DIGIT(rand2)) {
        Rational_L div(1, 1);
        if (rand1->v_type == V_INT)div.numerator = dynamic_cast<Integer *>(rand1.get())->n;
        else if (rand1->v_type == V_RATIONAL) {
            div.numerator = dynamic_cast<Rational *>(rand1.get())->numerator;
            div.denominator = dynamic_cast<Rational *>(rand1.get())->denominator;
        }
        if (rand2->v_type == V_INT) {
            if (dynamic_cast<Integer *>(rand2.get())->n != 0)div.denominator *= dynamic_cast<Integer *>(rand2.get())->n;
            else throw(RuntimeError("Division by zero"));
        } else if (rand2->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(rand2.get())->numerator,
                             dynamic_cast<Rational *>(rand2.get())->denominator);
            if (temp_RA.numerator == 0)throw(RuntimeError("Division by zero"));
            div.denominator *= temp_RA.numerator;
            div.numerator *= temp_RA.denominator;
        }
        return distribute(div);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) {
    // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer *>(rand1.get())->n;
        int divisor = dynamic_cast<Integer *>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) {
    // + with multiple args
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)if (!IS_DIGIT(args[i]))throw(RuntimeError("Wrong typename"));
    Rational_L sum(0, 1);
    if (args[0]->v_type == V_INT)sum.numerator = dynamic_cast<Integer *>(args[0].get())->n;
    else if (args[0]->v_type == V_RATIONAL) {
        sum.numerator = dynamic_cast<Rational *>(args[0].get())->numerator;
        sum.denominator = dynamic_cast<Rational *>(args[0].get())->denominator;
    }
    int temp_gcd;
    for (int i = 1; i < args.size(); i++) {
        if (args[i]->v_type == V_INT)sum.numerator += dynamic_cast<Integer *>(args[i].get())->n * sum.denominator;
        else if (args[i]->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(args[0].get())->numerator,
                             dynamic_cast<Rational *>(args[i].get())->denominator);
            int temp = std::__gcd(temp_RA.denominator, sum.denominator);
            temp = static_cast<int>(temp_RA.denominator) * sum.denominator / temp;
            sum.numerator *= temp / sum.denominator;
            sum.denominator = temp;
            sum.numerator += static_cast<int>(temp_RA.numerator) * temp / static_cast<int>(temp_RA.denominator);
            temp_gcd = std::__gcd(sum.numerator, sum.denominator);
            sum.numerator /= temp_gcd;
            sum.denominator /= temp_gcd;
        }
    }
    return distribute(sum);
}

Value MinusVar::evalRator(const std::vector<Value> &args) {
    // - with multiple args
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)if (!IS_DIGIT(args[i]))throw(RuntimeError("Wrong typename"));
    Rational_L difference(0, 1);
    if (args[0]->v_type == V_INT)difference.numerator = dynamic_cast<Integer *>(args[0].get())->n;
    else if (args[0]->v_type == V_RATIONAL) {
        difference.numerator = dynamic_cast<Rational *>(args[0].get())->numerator;
        difference.denominator = dynamic_cast<Rational *>(args[0].get())->denominator;
    }
    int temp_gcd;
    for (int i = 1; i < args.size(); i++) {
        if (args[i]->v_type == V_INT)
            difference.numerator -= dynamic_cast<Integer *>(args[i].get())->n * difference.
                    denominator;
        else if (args[i]->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(args[0].get())->numerator,
                             dynamic_cast<Rational *>(args[i].get())->denominator);
            int temp = std::__gcd(temp_RA.denominator, difference.denominator);
            temp = static_cast<int>(temp_RA.denominator) * difference.denominator / temp;
            difference.numerator *= temp / difference.denominator;
            difference.denominator = temp;
            difference.numerator -= static_cast<int>(temp_RA.numerator) * temp / static_cast<int>(temp_RA.denominator);
            temp_gcd = std::__gcd(difference.numerator, difference.denominator);
            difference.numerator /= temp_gcd;
            difference.denominator /= temp_gcd;
        }
    }
    return distribute(difference);
    //TODO: To complete the substraction logic
}

Value MultVar::evalRator(const std::vector<Value> &args) {
    // * with multiple args
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)if (!IS_DIGIT(args[i]))throw(RuntimeError("Wrong typename"));
    Rational_L mul(0, 1);
    if (args[0]->v_type == V_INT)mul.numerator = dynamic_cast<Integer *>(args[0].get())->n;
    else if (args[0]->v_type == V_RATIONAL) {
        mul.numerator = dynamic_cast<Rational *>(args[0].get())->numerator;
        mul.denominator = dynamic_cast<Rational *>(args[0].get())->denominator;
    }
    int temp_gcd;
    for (int i = 1; i < args.size(); i++) {
        if (args[i]->v_type == V_INT)mul.numerator *= dynamic_cast<Integer *>(args[i].get())->n;
        else if (args[i]->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(args[0].get())->numerator,
                             dynamic_cast<Rational *>(args[i].get())->denominator);
            mul.numerator *= temp_RA.numerator;
            mul.denominator *= temp_RA.denominator;
            temp_gcd = std::__gcd(mul.numerator, mul.denominator);
            mul.numerator /= temp_gcd;
            mul.denominator /= temp_gcd;
        }
    }
    return distribute(mul);
}

Value DivVar::evalRator(const std::vector<Value> &args) {
    // / with multiple args
    //TODO: To complete the divisor logic
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)if (!IS_DIGIT(args[i]))throw(RuntimeError("Wrong typename"));
    Rational_L div(0, 1);
    if (args[0]->v_type == V_INT)div.numerator = dynamic_cast<Integer *>(args[0].get())->n;
    else if (args[0]->v_type == V_RATIONAL) {
        div.numerator = dynamic_cast<Rational *>(args[0].get())->numerator;
        div.denominator = dynamic_cast<Rational *>(args[0].get())->denominator;
    }
    int temp_gcd;
    for (int i = 1; i < args.size(); i++) {
        if (args[i]->v_type == V_INT)div.denominator *= dynamic_cast<Integer *>(args[i].get())->n;
        else if (args[i]->v_type == V_RATIONAL) {
            Rational temp_RA(dynamic_cast<Rational *>(args[0].get())->numerator,
                             dynamic_cast<Rational *>(args[i].get())->denominator);
            div.numerator *= temp_RA.denominator;
            div.denominator *= temp_RA.numerator;
            temp_gcd = std::__gcd(div.numerator, div.denominator);
            div.numerator /= temp_gcd;
            div.denominator /= temp_gcd;
        }
    }
    return distribute(div);
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) {
    // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer *>(rand1.get())->n;
        int exponent = dynamic_cast<Integer *>(rand2.get())->n;

        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }

        int result = 1;
        int b = base;
        int exp = exponent;

        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }

        return IntegerV(result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer *>(v1.get())->n;
        int n2 = dynamic_cast<Integer *>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational *r1 = dynamic_cast<Rational *>(v1.get());
        int n2 = dynamic_cast<Integer *>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer *>(v1.get())->n;
        Rational *r2 = dynamic_cast<Rational *>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational *r1 = dynamic_cast<Rational *>(v1.get());
        Rational *r2 = dynamic_cast<Rational *>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) {
    // <
    //TODO: To complete the less logic
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (
            rand2->v_type == V_INT || rand2->v_type == V_RATIONAL)) {
        return BooleanV(compareNumericValues(rand1, rand2) == -1);
    }
    throw(RuntimeError("Wrong typename"));
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) {
    // <=
    //TODO: To complete the lesseq logic
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (
            rand2->v_type == V_INT || rand2->v_type == V_RATIONAL)) {
        return BooleanV(compareNumericValues(rand1, rand2) != 1);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) {
    // =
    //TODO: To complete the equal logic
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (
            rand2->v_type == V_INT || rand2->v_type == V_RATIONAL)) {
        return BooleanV(compareNumericValues(rand1, rand2) == 0);
    }
    throw(RuntimeError("Wrong typename"));
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) {
    // >=
    //TODO: To complete the greatereq logic
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (
            rand2->v_type == V_INT || rand2->v_type == V_RATIONAL)) {
        return BooleanV(compareNumericValues(rand1, rand2) != -1);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) {
    // >
    //TODO: To complete the greater logic
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (
            rand2->v_type == V_INT || rand2->v_type == V_RATIONAL)) {
        return BooleanV(compareNumericValues(rand1, rand2) == 1);
    }
    throw(RuntimeError("Wrong typename"));
}

Value LessVar::evalRator(const std::vector<Value> &args) {
    // < with multiple args
    //TODO: To complete the less logic
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)
        if (args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL)
            throw(
                RuntimeError("Wrong typename"));
    for (int i = 1; i < args.size(); i++)if (compareNumericValues(args[i - 1], args[i]) != -1)return BooleanV(false);
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) {
    // <= with multiple args
    //TODO: To complete the lesseq logic
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)
        if (args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL)
            throw(
                RuntimeError("Wrong typename"));
    for (int i = 1; i < args.size(); i++)if (compareNumericValues(args[i - 1], args[i]) == 1)return BooleanV(false);
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) {
    // = with multiple args
    //TODO: To complete the equal logic
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)
        if (args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL)
            throw(
                RuntimeError("Wrong typename"));
    for (int i = 1; i < args.size(); i++)if (compareNumericValues(args[i - 1], args[i]) != 0)return BooleanV(false);
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) {
    // >= with multiple args
    //TODO: To complete the greatereq logic
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)if (args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL)throw(
        RuntimeError("Wrong typename"));
    for (int i = 1; i < args.size(); i++)if (compareNumericValues(args[i - 1], args[i]) == -1)return BooleanV(false);
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) {
    // > with multiple args
    //TODO: To complete the greater logic
    if (args.empty())throw(RuntimeError("No parameter"));
    for (int i = 0; i < args.size(); i++)
        if (args[i]->v_type != V_INT && args[i]->v_type != V_RATIONAL)
            throw(
                RuntimeError("Wrong typename"));
    for (int i = 1; i < args.size(); i++)if (compareNumericValues(args[i - 1], args[i]) != 1)return BooleanV(false);
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) {
    // cons
    //TODO: To complete the cons logic
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) {
    // list function
    //TODO: To complete the list logic
    if (args.empty())return NullV();
    Value temp = PairV(args[args.size() - 1], NullV());
    for (int i = args.size() - 1; i >= 1; i--)temp = PairV(args[i - 1], temp);
    return temp;
    throw(RuntimeError("Unable to build a list"));
}

Value IsList::evalRator(const Value &rand) {
    // list?
    //TODO: To complete the list? logic
    if (rand->v_type == V_PAIR) {
        if (dynamic_cast<Pair *>(rand.get())->car->v_type == V_PAIR || dynamic_cast<Pair *>(rand.get())->cdr->v_type ==
            V_PAIR)
            return BooleanV(true);
    }
    return BooleanV(false);
}

Value Car::evalRator(const Value &rand) {
    // car
    //TODO: To complete the car logic
    if (rand->v_type == V_PAIR)return dynamic_cast<Pair *>(rand.get())->car;
    throw(RuntimeError("Not a pair for Car"));
}

Value Cdr::evalRator(const Value &rand) {
    // cdr
    //TODO: To complete the cdr logic
    if (rand->v_type == V_PAIR)return dynamic_cast<Pair *>(rand.get())->cdr;
    throw(RuntimeError("Not a pair for Cdr"));
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) {
    // set-car!
    //TODO: To complete the set-car! logic
    if (rand1->v_type == V_PAIR) {
        dynamic_cast<Pair *>(rand1.get())->car = rand2;
        return VoidV();
    }
    throw(RuntimeError("Not a Pair"));
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) {
    // set-cdr!
    //TODO: To complete the set-cdr! logic
    if (rand1->v_type == V_PAIR) {
        dynamic_cast<Pair *>(rand1.get())->cdr = rand2;
        return VoidV();
    }
    throw(RuntimeError("Not a Pair"));
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) {
    // eq?
    // 检查类型是否为 Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer *>(rand1.get())->n) == (dynamic_cast<Integer *>(rand2.get())->n));
    }
    // 检查类型是否为 Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean *>(rand1.get())->b) == (dynamic_cast<Boolean *>(rand2.get())->b));
    }
    // 检查类型是否为 Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol *>(rand1.get())->s) == (dynamic_cast<Symbol *>(rand2.get())->s));
    }
    // 检查类型是否为 Null 或 Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) {
    // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) {
    // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) {
    // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) {
    // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) {
    // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) {
    // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) {
    // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    Value temp = nullptr;
    for (Expr i: es) {
        temp = i->eval(e);
    }
    return temp;
    //TODO: To complete the begin logic
}

Value Syntaxtransit(const Syntax s, Assoc &e) {
    if (dynamic_cast<List *>(s.get())) {
        List *temp_sy = dynamic_cast<List *>(s.get());
        if (temp_sy->stxs.empty()) return NullV();
        if (dynamic_cast<List *>(temp_sy->stxs[temp_sy->stxs.size() - 1].get())) {
            Value temp = Syntaxtransit(temp_sy->stxs[temp_sy->stxs.size() - 1], e);
            for (int i = temp_sy->stxs.size() - 2; i >= 0; i--) {
                if (dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get()) &&
                    dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s.size() == 1 &&
                    dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s[0] == '.') {
                    continue;
                } else temp = PairV(Syntaxtransit(temp_sy->stxs[i], e), temp);
            }
            return temp;
        }
        else {
            if (dynamic_cast<SymbolSyntax *>(temp_sy->stxs[temp_sy->stxs.size() - 2].get())) {
                if (dynamic_cast<SymbolSyntax *>(temp_sy->stxs[temp_sy->stxs.size() - 2].get())->s.size() == 1 &&
                dynamic_cast<SymbolSyntax *>(temp_sy->stxs[temp_sy->stxs.size() - 2].get())->s[0] == '.') {
                    Value temp = Syntaxtransit(temp_sy->stxs[temp_sy->stxs.size() - 1], e);
                    for (int i = temp_sy->stxs.size() - 3; i >= 0; i--) {
                        if (dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get()) &&
                            dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s.size() == 1 &&
                            dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s[0] == '.') {
                            continue;
                            } else temp = PairV(Syntaxtransit(temp_sy->stxs[i], e), temp);
                    }
                    return temp;
                }
                else {
                    Value temp =PairV( Syntaxtransit(temp_sy->stxs[temp_sy->stxs.size() - 1], e),NullV());
                    for (int i = temp_sy->stxs.size() - 2; i >= 0; i--) {
                        if (dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get()) &&
                            dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s.size() == 1 &&
                            dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s[0] == '.') {
                            continue;
                            } else temp = PairV(Syntaxtransit(temp_sy->stxs[i], e), temp);
                    }
                    return temp;
                }
            }
            else {
                Value temp =PairV( Syntaxtransit(temp_sy->stxs[temp_sy->stxs.size() - 1], e),NullV());
                for (int i = temp_sy->stxs.size() - 2; i >= 0; i--) {
                    if (dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get()) &&
                        dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s.size() == 1 &&
                        dynamic_cast<SymbolSyntax *>(temp_sy->stxs[i].get())->s[0] == '.') {
                        continue;
                        } else temp = PairV(Syntaxtransit(temp_sy->stxs[i], e), temp);
                }
                return temp;
            }
        }
    }
    if (dynamic_cast<StringSyntax *>(s.get())) {
        return StringV(dynamic_cast<StringSyntax *>(s.get())->s);
    }
    if (dynamic_cast<RationalSyntax *>(s.get())) {
        return RationalV(dynamic_cast<RationalSyntax *>(s.get())->numerator,
                         dynamic_cast<RationalSyntax *>(s.get())->denominator);
    }
    if (dynamic_cast<Number *>(s.get())) {
        return IntegerV(dynamic_cast<Number *>(s.get())->n);
    }
    if (dynamic_cast<FalseSyntax *>(s.get())) {
        return BooleanV(false);
    }
    if (dynamic_cast<TrueSyntax *>(s.get())) {
        return BooleanV(true);
    }
    if (dynamic_cast<SymbolSyntax *>(s.get())) {
        return SymbolV(dynamic_cast<SymbolSyntax *>(s.get())->s);
    }
    throw(RuntimeError("Wrong in Quote"));
}

Value Quote::eval(Assoc &e) {
    return Syntaxtransit(s, e);
    //TODO: To complete the quote logic
}

Value AndVar::eval(Assoc &e) {
    // and with short-circuit evaluation
    //TODO: To complete the and logic
    Value temp = BooleanV(true);
    for (Expr ex: rands) {
        temp = ex->eval(e);
        if (temp->v_type != V_BOOL)continue;
        if (dynamic_cast<Boolean *>(temp.get())->b == false)return BooleanV(false);
    }
    return temp;
}

Value OrVar::eval(Assoc &e) {
    // or with short-circuit evaluation
    //TODO: To complete the or logic
    Value temp = BooleanV(false);
    for (Expr ex: rands) {
        temp = ex->eval(e);
        if (temp->v_type != V_BOOL)return temp;
        if (dynamic_cast<Boolean *>(temp.get())->b != false)return BooleanV(true);
    }
    return temp;
}

Value Not::evalRator(const Value &rand) {
    // not
    if (rand->v_type == V_BOOL)return BooleanV(!dynamic_cast<Boolean *>(rand.get())->b);
    if (rand->v_type != V_BOOL)return BooleanV(false);
    throw(RuntimeError("Wrong in Not"));
    //TODO: To complete the not logic
}

Value If::eval(Assoc &e) {
    if (cond->eval(e)->v_type != V_BOOL)return conseq->eval(e);
    else if (dynamic_cast<Boolean *>(cond->eval(e).get())->b == true)return conseq->eval(e);
    else return alter->eval(e);
    //TODO: To complete the if logic
}

Value Cond::eval(Assoc &env) {
    for (int i = 0; i < clauses.size(); i++) {
        if (clauses[i].empty())throw(RuntimeError("No predict?"));
        if (clauses[i][0]->eval(env)->v_type != V_BOOL ||
            clauses[i][0]->eval(env)->v_type == V_BOOL && dynamic_cast<Boolean *>(clauses[i][0]->eval(env).get())->b ==
            true) {
            for (int j = 1; j < clauses[i].size() - 1; j++) {
                clauses[i][0]->eval(env);
            }
            return clauses[i][clauses[i].size() - 1]->eval(env);
        }
    }
    throw(RuntimeError("Wrong in Cond"));
    //TODO: To complete the cond logic
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
    //TODO: To complete the lambda logic
}

Value Apply::eval(Assoc &e) {

    Value proc = rator->eval(e);
    if (proc.get() == nullptr || proc->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    Procedure *clos_ptr = dynamic_cast<Procedure *>(proc.get());

    // Argument evaluation
    std::vector<Value> args;
    for (Expr i: rand) args.push_back(i->eval(e));
    // If the closure represents a primitive implemented as a Variadic/Unary/Binary
    // expression (and was stored with an empty parameter list), call its
    // evalRator directly with the already-evaluated argument Values.
    if (args.size() != clos_ptr->parameters.size()) {
        // Try to handle primitives encoded as Expr bodies
        // Variadic primitives accept any number of args
        if (auto varNode = dynamic_cast<Variadic *>(clos_ptr->e.get())) {
            return varNode->evalRator(args);
        }
        // Binary primitives accept exactly two args
        if (auto binNode = dynamic_cast<Binary *>(clos_ptr->e.get())) {
            if (args.size() == 2) return binNode->evalRator(args[0], args[1]);
        }
        // Unary primitives accept exactly one arg
        if (auto unNode = dynamic_cast<Unary *>(clos_ptr->e.get())) {
            if (args.size() == 1) return unNode->evalRator(args[0]);
        }
        throw RuntimeError("Wrong number of arguments");
    }

    // Create a new environment frame extending the closure's environment
    Assoc param_env = clos_ptr->env;
    for (int i = 0; i < (int)clos_ptr->parameters.size(); i++) {
        // Use extend to add a fresh binding for each parameter with the corresponding argument value
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }
    // Evaluate the procedure body in the extended environment
    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // For function-definition shorthand and recursive definitions, we must
    // create a placeholder binding first so that the function body can
    // reference the function name (support simple recursion).
    if (dynamic_cast<Lambda *>(e.get())) {
        // create placeholder
        env = extend(var, NullV(), env);
        Value v = e->eval(env); // evaluate lambda in env that already contains placeholder
        modify(var, v, env);
        return VoidV();
    } else {
        env = extend(var, e->eval(env), env);
        return VoidV();
    }
}

Value Let::eval(Assoc &env) {
    Assoc param_env = env;
    for (int i = 0; i < bind.size(); i++) {
        param_env=extend(bind[i].first,bind[i].second->eval(env), param_env);
    }
    return body->eval(param_env);
    //TODO: To complete the let logic
}

Value Letrec::eval(Assoc &env) {
    Assoc e = env;
    for (int i = 0; i < bind.size(); i++)e = extend(bind[i].first, NullV(), e);
    Value s = nullptr;
    for (int i = 0; i < bind.size(); i++) {
        s = bind[i].second->eval(e);
        modify(bind[i].first, s, e);
    }
    return body->eval(e);
    //TODO: To complete the letrec logic
}

Value Set::eval(Assoc &env) {
    Value temp=e->eval(env);
    modify(var, temp, env);
    return VoidV();
    //TODO: To complete the set logic
}

Value Display::evalRator(const Value &rand) {
    // display function
    if (rand->v_type == V_STRING) {
        String *str_ptr = dynamic_cast<String *>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
