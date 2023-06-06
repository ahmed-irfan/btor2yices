 # 
 # This file is part of the BTOR2YICES distribution (https://github.com/btor2yices).
 # Copyright (c) 2023 Ahmed Irfan.
 # 
 # This program is free software: you can redistribute it and/or modify  
 # it under the terms of the GNU General Public License as published by  
 # the Free Software Foundation, version 3.
 #
 # This program is distributed in the hope that it will be useful, but 
 # WITHOUT ANY WARRANTY; without even the implied warranty of 
 # MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU 
 # General Public License for more details.
 #
 # You should have received a copy of the GNU General Public License 
 # along with this program. If not, see <http://www.gnu.org/licenses/>.
 #


from yices import *

class Btor2Parser(object):

    def __init__(self):
        self.symbol_table = {} # idx -> (term, sort)
        self.sorts = {} # idx -> sort
        self.inputs = {} # idx -> term
        self.states = {} # idx -> term, next term
        self.outputs = {} # idx -> term
        self.init = {} # idx -> term
        self.constraints = {} # idx -> term
        self.bad = {} # idx -> term
        self.tmap = {} 
        self.init_tmap()

    def init_tmap(self):
        self.tmap = {
            "init" : self._parse_init,
            "next" : self._parse_next,
            "bad" : self._parse_bad,
            "constraint" : self._parse_constraint,
            "output" : self._parse_output,
            "add" : self._parse_bin_op(Terms.bvadd),
            "mul" : self._parse_bin_op(Terms.bvmul),
            "sdiv" : self._parse_bin_op(Terms.bvsdiv),
            "udiv" : self._parse_bin_op(Terms.bvdiv),
            "smod" : self._parse_bin_op(Terms.bvsmod),
            "srem" : self._parse_bin_op(Terms.bvsrem),
            "urem" : self._parse_bin_op(Terms.bvrem),
            "sub" : self._parse_bin_op(Terms.bvsub),
            "and" : self._parse_bin_op(Terms.bvand, True),
            "nand" : self._parse_bin_op(Terms.bvnand),
            "nor" : self._parse_bin_op(Terms.bvnor),
            "or" : self._parse_bin_op(Terms.bvor, True),
            "xnor" : self._parse_bin_op(Terms.bvxnor),
            "xor" : self._parse_bin_op(Terms.bvxor, True),
            "concat" : self._parse_bin_op(Terms.bvconcat, True),
            "sll" : self._parse_bin_op(Terms.bvshl),
            "sra" : self._parse_bin_op(Terms.bvashr),
            "srl" : self._parse_bin_op(Terms.bvlshr),
            "eq" : self._parse_bin_op_bool(Terms.eq),
            "neq" : self._parse_bin_op_bool(Terms.neq),
            "sgt" : self._parse_bin_op_bool(Terms.bvsgt_atom),
            "sgte" : self._parse_bin_op_bool(Terms.bvsge_atom),
            "slt" : self._parse_bin_op_bool(Terms.bvslt_atom),
            "slte" : self._parse_bin_op_bool(Terms.bvsle_atom),
            "ugt" : self._parse_bin_op_bool(Terms.bvgt_atom),
            "ugte" : self._parse_bin_op_bool(Terms.bvge_atom),
            "ult" : self._parse_bin_op_bool(Terms.bvlt_atom),
            "ulte" : self._parse_bin_op_bool(Terms.bvle_atom),
            "redand" : self._parse_unary_op(Terms.redand),
            "redor" : self._parse_unary_op(Terms.redor),
            "redxor" : self._parse_redxor,
            "neg" : self._parse_unary_op(Terms.bvneg),
            "not" : self._parse_unary_op(Terms.bvnot),
            "iff" : self._parse_iff,
            "implies" : self._parse_implies,
            "const" : self._parse_const,
            "constd" : self._parse_constd,
            "consth" : self._parse_consth,
            "dec" : self._parse_dec,
            "ite" : self._parse_ite,
            "inc" : self._parse_inc,
            "input" : self._parse_input,
            "one" : self._parse_one,
            "ones" : self._parse_ones,
            "read" : self._parse_read,
            "rol" : self._parse_rol,
            "ror" : self._parse_ror,
            "sext" : self._parse_sext,
            "slice" : self._parse_slice,
            "sort" : self._parse_sort,
            "state" : self._parse_state,
            "write" : self._parse_write,
            "uext" : self._parse_uext,
            "zero" : self._parse_zero
            }

    def _get_term(self, idx, bool_context=False):
        i = int(idx)
        is_neg = i < 0
        idx = str(abs(i))
        term = self.symbol_table[idx][0]
        t = self.symbol_table[idx][1]
        if is_neg:
            if Types.is_bool(t):
                term = Terms.ynot(term)
            else:
                term = Terms.bvnot(term)
        if bool_context and not Types.is_bool(t):
            assert(Types.bvtype_size(t) == 1)
            term = Terms.bitextract(term, 0)
        if not bool_context and Types.is_bool(t):
            term = Terms.ite(term, Terms.bvconst_one(1), Terms.bvconst_zero(1))
        return term

    def _get_term_sort(self, idx):
        idx = str(abs(int(idx)))
        return self.symbol_table[idx][1]
    
    def _get_term2(self, idx1, idx2):
        term1 = self._get_term(idx1)
        term2 = self._get_term(idx2)
        return (term1, term2)

    def _parse_bin_op(self, yfun, is_arg_list=False):
        def f(idx, s, elem1, elem2, *r):
            term1, term2 = self._get_term2(elem1, elem2)
            term = yfun([term1, term2]) if is_arg_list else yfun(term1, term2) 
            self.symbol_table[idx] = (term, self.sorts[s])
        return f

    def _parse_bin_op_bool(self, yfun, is_arg_list=False):
        def f(idx, s, elem1, elem2, *r):
            term1, term2 = self._get_term2(elem1, elem2)
            term = yfun([term1, term2]) if is_arg_list else yfun(term1, term2) 
            self.symbol_table[idx] = (term, Types.bool_type())
        return f

    def _parse_unary_op(self, yfun):
        def f(idx, s, elem, *r):
            term = yfun(self._get_term(elem))
            self.symbol_table[idx] = (term, self.sorts[s])
        return f
    
    def _mk_bv_sort(self, idx, width):
        assert(int(width) > 0)
        t = Types.bv_type(int(width))
        self.sorts[idx] = t

    def _mk_array_sort(self, idx, s1, s2, *r):
        t1 = self.sorts[s1]
        t2 = self.sorts[s2]
        t = Types.new_function_type([t1], t2)
        self.sorts[idx] = t

    def _parse_init(self, idx, s, elem1, elem2, *r):
        term1, term2 = self._get_term2(elem1, elem2)
        self.init[elem1] = (term1, term2)
        self.symbol_table[idx] = (term2, self.sorts[s])

    def _parse_next(self, idx, s, elem1, elem2, *r):
        term1, term2 = self._get_term2(elem1, elem2)
        assert(self.states[elem1] == (term1, None))
        self.states[elem1] = (term1, term2)
        self.symbol_table[idx] = (term2, self.sorts[s])

    def _parse_bad(self, idx, elem, *r):
        term = self._get_term(elem, True)
        self.bad[idx] = term
        self.symbol_table[idx] = (term, Types.bool_type())

    def _parse_constraint(self, idx, elem, *r):
        term = self._get_term(elem, True)
        self.constraints[idx] = term
        self.symbol_table[idx] = (term, Types.bool_type())

    def _parse_output(self, idx, elem, *r):
        term = self._get_term(elem)
        self.outputs[idx] = term
        self.symbol_table[idx] = (term, Terms.type_of_term(term))

    def _parse_ite(self, idx, s, cond, case1, case2, *r):
        cond_term = self._get_term(cond, True)
        case1_term = self._get_term(case1)
        case2_term = self._get_term(case2)
        term = Terms.ite(cond_term, case1_term, case2_term)
        self.symbol_table[idx] = (term, self.sorts[s])
        
    def _parse_input(self, idx, s, name="", *r):
        if name == "":
            name = str(len(self.inputs))
        t = self.sorts[s]
        term = Terms.new_uninterpreted_term(t, "i_" + name)
        self.inputs[idx] = term
        self.symbol_table[idx] = (term, t)

    def _parse_read(self, idx, s, elem1, elem2, *r):
        term1 = self._get_term(elem1)
        term2 = self._get_term(elem2)
        term = Terms.application(term1, [term2])
        self.symbol_table[idx] = (term, self.sorts[s])
    
    def _parse_rol(self, idx, s, elem, n, *r):
        term = Terms.rotate_left(self._get_term(elem), int(n))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_ror(self, idx, s, elem, n, *r):
        term = Terms.rotate_right(self._get_term(elem), int(n))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_sort(self, idx, s, n1, n2=None, *r):
        if s == 'bitvec':
            self._mk_bv_sort(idx, n1)
        elif s == 'array':
            assert(n2 is not None)
            self._mk_array_sort(idx, n1, n2)
        else:
            assert(False)

    def _parse_state(self, idx, s, name="", *r):
        if name == "":
            name = str(len(self.states))
        t = self.sorts[s]
        term = Terms.new_uninterpreted_term(t, "s_" + name)
        self.states[idx] = (term, None)
        self.symbol_table[idx] = (term, t)

    def _parse_zero(self, idx, s, *r):
        term = Terms.bvconst_zero(Types.bvtype_size(self.sorts[s]))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_one(self, idx, s, *r):
        term = Terms.bvconst_one(Types.bvtype_size(self.sorts[s]))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_ones(self, idx, s, *r):
        term = Terms.bvconst_minus_one(Types.bvtype_size(self.sorts[s]))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_const(self, idx, s, num, *r):
        t = self.sorts[s]
        term = Terms.parse_bvbin(num)
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_constd(self, idx, s, num, *r):
        t = self.sorts[s]
        width = Types.bvtype_size(t)
        term = Terms.bvconst_integer(width, num)
        self.symbol_table[idx] = (term, self.sorts[s])
        
    def _parse_consth(self, idx, s, num, *r):
        t = self.sorts[s]
        term = Terms.parse_bvhex(num)
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_sext(self, idx, s, elem, n, *r):
        term = Terms.sign_extend(self._get_term(elem), int(n))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_uext(self, idx, s, elem, n, *r):
        term = Terms.zero_extend(self._get_term(elem), int(n))
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_slice(self, idx, s, elem, u, l, *r):
        i, j = int(l), int(u)
        assert(i <= j)
        assert(j < Types.bvtype_size(self._get_term_sort(elem)))
        term = Terms.bvextract(self._get_term(elem), i , j)
        self.symbol_table[idx] = (term, self.sorts[s])

    def _parse_iff(self, idx, s, elem1, elem2, *r):
        term1 = self._get_term(elem1, True)
        term2 = self._get_term(elem2, True)
        term = Terms.iff(term1, term2)
        self.symbol_table[idx] = (term, Types.bool_type())

    def _parse_implies(self, idx, s, elem1, elem2, *r):
        term1 = self._get_term(elem1, True)
        term2 = self._get_term(elem2, True)
        term = Terms.implies(term1, term2)
        self.symbol_table[idx] = (term, Types.bool_type())
        
    def _parse_inc(self, idx, s, elem, *r):
        t = self.sorts[s]
        one = Terms.bvconst_one(Types.bvtype_size(t))
        term = Terms.bvadd(self._get_term(elem), one)
        self.symbol_table[idx] = (term, t)

    def _parse_dec(self, idx, s, elem, *r):
        t = self.sorts[s]
        one = Terms.bvconst_one(Types.bvtype_size(t))
        term = Terms.bvsub(self._get_term(elem), one)
        self.symbol_table[idx] = (term, t)

    def _parse_redxor(self, idx, s, elem, *r):
        elem_term = self._get_term(elem)
        t = self._get_term_sort(elem)
        width = Types.bvtype_size(t)
        args = [Terms.bvextract(elem_term, i, i) for i in range(width)]
        term = Terms.bvxor(args)
        self.symbol_table[idx] = (term, self.sorts[s])
        
    def _parse_write(self, idx, s, a, i, v, *r):
        a_term = self._get_term(a)
        i_term = self._get_term(i)
        v_term = self._get_term(v)
        term = Terms.update(a_term, [i_term], v_term)
        self.symbol_table[idx] = (term, self.sorts[s])

    def parse(self, filename):
        with open(filename, "r") as f:
            line = f.readline().strip()
            while line:
                if not line or line.startswith(";"):
                    line = f.readline().strip()
                    continue
                #print(line)
                tokens = line.split()
                idx = tokens[0]
                op = tokens[1]
                fun = self.tmap[op]
                args = [idx] + tokens[2:]
                fun(*args)
                line = f.readline().strip()

    def print(self):
        print("##### INPUTS #####")
        for idx in self.inputs:
            print(Terms.to_string(self.inputs[idx]))

        print("##### STATES #####")
        for idx in self.states:
            print(Terms.to_string(self.states[idx][0]))

        print("##### OUTPUTS #####")
        for idx in self.outputs:
            print(Terms.to_string(self.outputs[idx]))

        print("##### CONSTRAINTS #####")
        for idx in self.constraints:
            print(Terms.to_string(self.constraints[idx]))

        print("##### INIT #####")
        for idx in self.init:
            print(Terms.to_string(self.init[idx][0]) + " := " + \
                  Terms.to_string(self.init[idx][1]))

        print("##### NEXT #####")
        for idx in self.states:
            if self.states[idx][1] != None:
                print("next(" + Terms.to_string(self.states[idx][0]) + ") := " + \
                      Terms.to_string(self.states[idx][1]))

        print("##### BAD #####")
        for idx in self.bad:
            print(Terms.to_string(self.bad[idx]))

if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser()
    
    p.add_argument('fname', help='input btor2 filename')

    opts = p.parse_args()

    btor2parser = Btor2Parser()
    btor2parser.parse(opts.fname)

    btor2parser.print()
