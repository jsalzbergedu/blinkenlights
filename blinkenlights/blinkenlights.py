#!/usr/bin/python3
import sqlite3
import pycparser
import sys
import json
import os

def new_no(con, idt, tbl):
    return ([x[0] for x in con.execute("""select {} from {} order by {} desc limit 1""".format(idt, tbl, idt))] + [0])[0] + 1

def new_nodeno(con):
    return new_no(con, "id", "node")

def new_fileinfo(con):
    return new_no(con, "id", "fileinfo")

def new_childno(con):
    return new_no(con, "id", "children")

def new_exprno(con):
    return new_no(con, "id", "expr")

def new_expr_childno(con):
    return new_no(con, "id", "expr_children")

def new_variableno(con):
    return new_no(con, "id", "variable")

def new_constantno(con):
    return new_no(con, "id", "constant")

def parse_expr_dispatch(con, pycobj):
    if type(pycobj) == pycparser.c_ast.ID:
        return parse_id(con, pycobj)
    elif type(pycobj) == pycparser.c_ast.Constant:
        return parse_constant(con, pycobj)
    elif type(pycobj) == pycparser.c_ast.BinaryOp and pycobj.op == '>=':
        return parse_ge(con, pycobj)
    elif type(pycobj) == pycparser.c_ast.BinaryOp and pycobj.op == '+':
        return parse_ge(con, pycobj)
    elif type(pycobj) == pycparser.c_ast.BinaryOp and pycobj.op == '>':
        return parse_gt(con, pycobj)
    else:
        raise ValueError(type(pycobj).__name__ + " not yet implemented")

def parse_id(con, pycid):
    variableno = new_variableno(con)
    con.execute('''insert into variable values (:idt, :name)''',
                {"idt": variableno, "name": pycid.name})
    exprno = new_exprno(con)
    con.execute('''insert into expr values (:kind, :id)''',
                {"kind": "variable", "id": exprno})
    expr_childno = new_expr_childno(con)
    con.execute('''insert into expr_children values (:id, :expr, :idx, :child)''',
                {"id": expr_childno, "expr": exprno, "idx": 0, "child": variableno})
    con.commit()
    return exprno

def parse_constant(con, pycconst):
    constantno = new_constantno(con)
    con.execute('''insert into constant values (:idt, :constant)''',
                {"idt": constantno, "constant": pycconst.value})
    exprno = new_exprno(con)
    con.execute('''insert into expr values (:kind, :id)''',
                {"kind": "constant", "id": exprno})
    expr_childno = new_expr_childno(con)
    con.execute('''insert into expr_children values (:id, :expr, :idx, :child)''',
                {"id": expr_childno, "expr": exprno, "idx": 0, "child": constantno})
    con.commit()
    return exprno

def parse_ge(con, pycbinop):
    exprno = new_exprno(con)
    con.execute('''insert into expr values (:kind, :idt)''',
                {"kind": "ge", "idt": exprno})
    left_child = parse_expr_dispatch(con, pycbinop.left)
    childid = new_expr_childno(con)
    con.execute('''insert into expr_children values (:idt, :expr, :idx, :child)''',
                {"idt": childid, "expr": exprno, "idx": 0, "child": left_child})
    right_child = parse_expr_dispatch(con, pycbinop.right)
    childid = new_expr_childno(con)
    con.execute('''insert into expr_children values (:idt, :expr, :idx, :child)''',
                {"idt": childid, "expr": exprno, "idx": 1, "child": right_child})
    con.commit()
    return exprno

def parse_gt(con, pycbinop):
    exprno = new_exprno(con)
    con.execute('''insert into expr values (:kind, :idt)''',
                {"kind": "gt", "idt": exprno})
    left_child = parse_expr_dispatch(con, pycbinop.left)
    childid = new_expr_childno(con)
    con.execute('''insert into expr_children values (:idt, :expr, :idx, :child)''',
                {"idt": childid, "expr": exprno, "idx": 0, "child": left_child})
    right_child = parse_expr_dispatch(con, pycbinop.right)
    childid = new_expr_childno(con)
    con.execute('''insert into expr_children values (:idt, :expr, :idx, :child)''',
                {"idt": childid, "expr": exprno, "idx": 1, "child": right_child})
    con.commit()
    return exprno

def parse_plus(con, pycbinop):
    exprno = new_exprno(con)
    con.execute('''insert into expr values (:kind, :idt)''',
                {"kind": "+", "idt": exprno})
    left_child = parse_expr_dispatch(con, pycbinop.left)
    childid = new_expr_childno(con)
    con.execute('''insert into expr_children values (:idt, :expr, :idx, :child)''',
                {"idt": childid, "expr": exprno, "idx": 0, "child": left_child})
    right_child = parse_expr_dispatch(con, pycbinop.right)
    childid = new_expr_childno(con)
    con.execute('''insert into expr_children values (:idt, :expr, :idx, :child)''',
                {"idt": childid, "expr": exprno, "idx": 1, "child": right_child})
    con.commit()
    return exprno

def parse_dispatch(pycobj, con):
    if type(pycobj) == pycparser.c_ast.Compound:
        return parse_compound(pycobj, con)
    elif type(pycobj) == pycparser.c_ast.Break:
        return parse_break(pycobj, con)
    elif type(pycobj) == pycparser.c_ast.If and not pycobj.iffalse:
        return parse_ifthen(pycobj, con)
    elif type(pycobj) == pycparser.c_ast.If:
        return parse_ifthenelse(pycobj, con)
    elif type(pycobj) == pycparser.c_ast.While:
        return parse_while(pycobj, con)
    elif type(pycobj) == pycparser.c_ast.Assignment:
        return parse_assign(pycobj, con)
    elif type(pycobj) == pycparser.c_ast.Decl:
        return parse_decl(pycobj, con)
    else:
        raise ValueError(type(pycobj).__name__ + " not yet handled")

def parse_pycobj(pycobj, kind, con):
    idno = new_nodeno(con)
    con.execute('''insert into node values (:kind , :idno)''',
                {"kind": kind, "idno": idno})
    fileid = new_fileinfo(con)
    filename = pycobj.coord.file
    column = pycobj.coord.column
    line = pycobj.coord.line
    con.execute('''insert into fileinfo values (:id, :filename, :column, :line, :node)''',
                {"id": fileid, "filename": filename, "column": column, "line": line, "node": idno})
    con.commit()
    return idno

def parse_break(pycbreak, con):
    return parse_pycobj(pycbreak, "break", con)

def parse_decl(pycdecl, con):
    return parse_pycobj(pycdecl, "decl", con)

def parse_compound(pyccompound, con):
    idno = parse_pycobj(pyccompound, "compound", con)
    child = parse_compound_rec(idno, pyccompound.children(), con)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 0, "child": child})
    con.commit()
    return idno

def parse_compound_rec(idno, children, con):
    # Get filename, column, line for base cases
    filename, column, line = [x for x in con.execute('''select filename, column, line from fileinfo where node=:idno''', {"idno": idno})][0]
    if (len(children) == 0):
        idno = new_nodeno(con)
        con.execute('''insert into node values (:kind , :idno)''',
                    {"kind": "empty", "idno": idno})
        fileid = new_fileinfo(con)
        con.execute('''insert into fileinfo values (:idt, :filename, :column, :line, :node)''',
                    {"idt": fileid, "filename": filename, "column": column, "line": line, "node": idno})
        con.commit()
        return idno
    elif (len(children) == 1):
        # Insert Sl
        idno = new_nodeno(con)
        con.execute('''insert into node values (:kind , :idno)''',
                    {"kind": "sl", "idno": idno})
        fileid = new_fileinfo(con)
        con.execute('''insert into fileinfo values (:idt, :filename, :column, :line, :node)''',
                    {"idt": fileid, "filename": filename, "column": column, "line": line, "node": idno})
        # Insert empty Sl
        left = parse_compound_rec(idno, (), con)
        childid = new_childno(con)
        con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                    {"idt": childid, "node": idno, "idx": 0, "child": left})
        # Insert right Sl
        right_pycobj = children[0][1]
        right = parse_dispatch(right_pycobj, con)
        childid = new_childno(con)
        con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                    {"idt": childid, "node": idno, "idx": 1, "child": right})
        con.commit()
        return idno
    else:
        # Insert Sl
        idno = new_nodeno(con)
        con.execute('''insert into node values (:kind , :idno)''',
                    {"kind": "sl", "idno": idno})
        fileid = new_fileinfo(con)
        con.execute('''insert into fileinfo values (:idt, :filename, :column, :line, :node)''',
                    {"idt": fileid, "filename": filename, "column": column, "line": line, "node": idno})
        # Insert right Sl
        right_pycobj = children[-1][1]
        right = parse_dispatch(right_pycobj, con)
        childid = new_childno(con)
        con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                    {"idt": childid, "node": idno, "idx": 1, "child": right})
        con.commit()
        # Process left Sl
        left = parse_compound_rec(idno, children[:-1], con)
        childid = new_childno(con)
        con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                    {"idt": childid, "node": idno, "idx": 0, "child": left})
        return idno

def parse_assign(pycassign, con):
    idno = parse_pycobj(pycassign, "assign", con)
    left = parse_expr_dispatch(con, pycassign.lvalue)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 0, "child": left})
    right = parse_expr_dispatch(con, pycassign.rvalue)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 1, "child": right})
    con.commit()
    return idno

def parse_while(pycwhile, con):
    idno = parse_pycobj(pycwhile, "while", con)
    child = parse_expr_dispatch(con, pycwhile.cond)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 0, "child": child})
    child = parse_dispatch(pycwhile.stmt, con)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 1, "child": child})
    con.commit()
    return idno

def parse_ifthen(pycifthen, con):
    idno = parse_pycobj(pycifthen, "ifthen", con)
    child = parse_expr_dispatch(con, pycifthen.cond)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 0, "child": child})
    child = parse_dispatch(pycifthen.iftrue, con)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 1, "child": child})
    con.commit()
    return idno

def parse_ifthenelse(pycifthenelse, con):
    idno = parse_pycobj(pycifthenelse, "ifthenelse", con)
    child = parse_expr_dispatch(con, pycifthenelse.cond)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 0, "child": child})
    child = parse_dispatch(pycifthenelse.iftrue, con)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 1, "child": child})
    child = parse_dispatch(pycifthenelse.iffalse, con)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 2, "child": child})
    con.commit()
    return idno

def parse_program(pycprogram, con):
    idno = parse_pycobj(pycprogram, "pgm", con)
    child = parse_dispatch(pycprogram, con)
    childid = new_childno(con)
    con.execute('''insert into children values (:idt, :node, :idx, :child)''',
                {"idt": childid, "node": idno, "idx": 0, "child": child})
    con.commit()
    return idno

def get_node_node_child(con, idt, idx):
    return [x for x in con.execute("select dest.id from node source inner join children on source.id=children.node AND children.idx=:idx left join node dest on children.child=dest.id where source.id=:idt", {"idt": idt, "idx": idx})][0][0]

def get_node_expr_child(con, idt, idx):
    return [x for x in con.execute("select dest.id from node source inner join children on source.id=children.node AND children.idx=:idx left join expr dest on children.child=dest.id where source.id=:idt", {"idt": idt, "idx": idx})][0][0]

def get_kind(con, idt):
    return [x for x in con.execute("select kind from node where id=:idt", {"idt": idt})][0][0]

def dispatch_command(command, con):
    if command["command"] == 'parse':
        parsed = pycparser.parse_file(os.path.abspath(command["filename"]), use_cpp=True, cpp_path='gcc', cpp_args=['-E'])
        program = parsed.ext[0].body
        rval = {"node": parse_program(program, con)}
        con.commit()
        return rval
    elif command["command"] == 'get_kind':
        return {"kind": get_kind(con, command["idt"])}
    elif command["command"] == 'get_child':
        return {"kind": get_kind(con, command["idt"])}
    else:
        raise ValueError("Command ", command, "not handled")

def setup_con():
    con = sqlite3.connect('analysis.db')
    con.execute('''CREATE TABLE IF NOT EXISTS node (kind text, id integer, PRIMARY KEY (id))''')
    con.execute('''CREATE TABLE IF NOT EXISTS fileinfo (id integer, filename text, column text, line text, node integer, PRIMARY KEY (id))''')
    con.execute('''CREATE TABLE IF NOT EXISTS children (id integer, node integer, idx integer, child integer, PRIMARY KEY (id))''')
    con.execute('''CREATE TABLE IF NOT EXISTS expr (kind text, id integer, PRIMARY KEY (id))''')
    con.execute('''CREATE TABLE IF NOT EXISTS expr_children (id integer, expr integer, idx integer, child integer, PRIMARY KEY (id))''')
    con.execute('''CREATE TABLE IF NOT EXISTS variable (id integer, name text, PRIMARY KEY (id))''')
    con.execute('''CREATE TABLE IF NOT EXISTS constant (id integer, constant integer, PRIMARY KEY (id))''')
    con.commit()
    return con

if __name__ == '__main__':
    con = setup_con()
    while True:
        line = sys.stdin.read()
        if not line:
            break
        command = json.loads(line)
        print(json.dumps(dispatch_command(command, con)))
    con.close()


