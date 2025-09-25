#!/usr/bin/python3 -B

out = ""

def tokenize(lines):
    lines = lines.replace("(", " ( ").replace(")", " ) ").replace("[", " [ ").replace("]", " ] ")

    full = ""
    for line in lines.split("\n"):
        i = line.find(";")
        if i == -1:
            full += line
        elif i > 0:
            full += line[:i-1]
    return [x for x in full.split() if x != ""]

def deop(x):
    if x == "+":
        return "Add"
    if x == "-":
        return "Sub"
    if x == "*":
        return "Mul"
    if x == "/":
        return "Div"
    if x == "0":
        return "Zero"
    if x == "1":
        return "One"
    if x == "-1":
        return "NegOne"
    if x == "2":
        return "Two"
    if x == "-2":
        return "NegTwo"
    if x == "3":
        return "Three"
    if x == "1/2":
        return "AHalf"
    if x in ["x", "y", "z", "a", "b", "c"]:
        return x
    return x.capitalize()

def reformat_term(toks):
    global out
    if toks[0] != "(":
        out += deop(toks[0])
        return toks[1:]

    assert(toks[0] == "(")
    toks = toks[1:]
    out += deop(toks[0]) + "("
    toks = toks[1:]
    while toks[0] != ")":
        toks = reformat_term(toks)
        out += ","
    out = out[:len(out)-1]
    out += ")"
    return toks[1:]

def reformat_line(toks):
    global out

    toks = toks[1:]
    toks = reformat_term(toks)
    out += " = "
    toks = reformat_term(toks)
    match toks:
        case []: pass
        case ["#:unsound"]: pass
        case _:
            print(toks)
            raise OhNo
    out += "\n"

def reformat(toks):
    while len(toks) > 0:
        match toks:
            case ["(", "define-rules", name, *toks]:
                while len(toks) > 0 and toks[0] == "[":
                    end = toks.index("]")
                    line = toks[1:end]
                    reformat_line(line)
                    toks = toks[end+1:]
                assert(toks[0] == ")")
                toks = toks[1:]
            case _:
                raise OhNo

def main():
    lines = open("rules.rkt").read()
    toks = tokenize(lines)
    reformat(toks)
    print(out)

main()
