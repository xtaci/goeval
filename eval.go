package goeval

import (
	"errors"
	"fmt"
	//	"github.com/davecgh/go-spew/spew"
	"go/ast"
	"go/parser"
	"go/token"
	"reflect"
	"strconv"
)

var (
	Builtins = map[string]interface{}{
		"nil":    nil,
		"true":   true,
		"false":  false,
		"append": Append,
		"make":   Make,
		"len":    Len,
	}
)

// variable scope, recursive definition
type Scope struct {
	Vals   map[string]interface{} // all variables in current scope
	Parent *Scope
}

// create a new variable scope
func NewScope() *Scope {
	s := &Scope{
		Vals: map[string]interface{}{},
	}
	return s
}

// search variable from inner-most scope
func (scope *Scope) Get(name string) (val interface{}) {
	currentScope := scope
	exists := false
	for !exists && currentScope != nil {
		val, exists = currentScope.Vals[name]
		currentScope = currentScope.Parent
	}
	return
}

// Set walks the scope and sets a value in a parent scope if it exists, else current.
func (scope *Scope) Set(name string, val interface{}) {
	exists := false
	currentScope := scope
	for !exists && currentScope != nil {
		_, exists = currentScope.Vals[name]
		if exists {
			currentScope.Vals[name] = val
		}
		currentScope = currentScope.Parent
	}
	if !exists {
		scope.Vals[name] = val
	}
}

// Keys returns all keys in scope
func (scope *Scope) Keys() (keys []string) {
	currentScope := scope
	for currentScope != nil {
		for k := range currentScope.Vals {
			keys = append(keys, k)
		}
		currentScope = scope.Parent
	}
	return
}

// NewChild creates a scope under the existing scope.
func (scope *Scope) NewChild() *Scope {
	s := NewScope()
	s.Parent = scope
	return s
}

// Eval evaluates a string
func (s *Scope) Eval(str string) (interface{}, error) {
	expr, err := parser.ParseExpr("func(){" + str + "}()")
	if err != nil {
		return nil, err
	}
	return s.Interpret(expr.(*ast.CallExpr).Fun.(*ast.FuncLit).Body)
}

// Interpret interprets an ast.Node and returns the value.
func (scope *Scope) Interpret(expr ast.Node) (interface{}, error) {
	switch e := expr.(type) {
	case *ast.Ident: // An Ident node represents an identifier.
		typ, err := StringToType(e.Name)
		if err == nil {
			return typ, err
		}

		if obj, exists := Builtins[e.Name]; exists {
			return obj, nil
		}

		if obj := scope.Get(e.Name); obj != nil {
			return obj, nil
		}
		return nil, fmt.Errorf("can't find EXPR %s", e.Name)

	case *ast.SelectorExpr: // A SelectorExpr node represents an expression followed by a selector.
		X, err := scope.Interpret(e.X)
		if err != nil {
			return nil, err
		}
		sel := e.Sel

		rVal := reflect.ValueOf(X)
		if rVal.Kind() != reflect.Struct && rVal.Kind() != reflect.Ptr {
			return nil, fmt.Errorf("%#v is not a struct and thus has no field %#v", X, sel.Name)
		}

		if method := rVal.MethodByName(sel.Name); method.IsValid() {
			return method.Interface(), nil
		}
		if rVal.Kind() == reflect.Ptr {
			rVal = rVal.Elem()
		}
		if field := rVal.FieldByName(sel.Name); field.IsValid() {
			return field.Interface(), nil
		}
		return nil, fmt.Errorf("unknown field %#v", sel.Name)

	case *ast.CallExpr:
		fun, err := scope.Interpret(e.Fun)
		if err != nil {
			return nil, err
		}

		// make sure fun is a function
		rf := reflect.ValueOf(fun)
		if rf.Kind() != reflect.Func {
			return nil, fmt.Errorf("Not a function %#v", fun)
		}

		// interpret args
		args := make([]reflect.Value, len(e.Args))
		for i, arg := range e.Args {
			interpretedArg, err := scope.Interpret(arg)
			if err != nil {
				return nil, err
			}
			args[i] = reflect.ValueOf(interpretedArg)
		}

		// call
		values := ValuesToInterfaces(rf.Call(args))
		if len(values) == 0 {
			return nil, nil
		} else if len(values) == 1 {
			return values[0], nil
		}
		err, _ = values[1].(error)
		return values[0], err

	case *ast.BasicLit:
		switch e.Kind {
		case token.INT:
			n, err := strconv.ParseInt(e.Value, 0, 64)
			return int(n), err
		case token.FLOAT, token.IMAG:
			return strconv.ParseFloat(e.Value, 64)
		case token.CHAR:
			return (rune)(e.Value[1]), nil
		case token.STRING:
			return e.Value[1 : len(e.Value)-1], nil
		default:
			return nil, fmt.Errorf("unknown basic literal %d", e.Kind)
		}

	case *ast.CompositeLit:
		typ, err := scope.Interpret(e.Type)
		if err != nil {
			return nil, err
		}

		switch t := e.Type.(type) {
		case *ast.ArrayType:
			l := len(e.Elts)
			slice := reflect.MakeSlice(typ.(reflect.Type), l, l)
			for i, elem := range e.Elts {
				elemValue, err := scope.Interpret(elem)
				if err != nil {
					return nil, err
				}
				slice.Index(i).Set(reflect.ValueOf(elemValue))
			}
			return slice.Interface(), nil

		case *ast.MapType:
			nMap := reflect.MakeMap(typ.(reflect.Type))
			for _, elem := range e.Elts {
				switch eT := elem.(type) {
				case *ast.KeyValueExpr:
					key, err := scope.Interpret(eT.Key)
					if err != nil {
						return nil, err
					}
					val, err := scope.Interpret(eT.Value)
					if err != nil {
						return nil, err
					}
					nMap.SetMapIndex(reflect.ValueOf(key), reflect.ValueOf(val))

				default:
					return nil, fmt.Errorf("invalid element type %#v to map. Expecting key value pair", eT)
				}
			}
			return nMap.Interface(), nil

		default:
			return nil, fmt.Errorf("unknown composite literal %#v", t)
		}

	case *ast.BinaryExpr:
		x, err := scope.Interpret(e.X)
		if err != nil {
			return nil, err
		}
		y, err := scope.Interpret(e.Y)
		if err != nil {
			return nil, err
		}
		return ComputeBinaryOp(x, y, e.Op)

	case *ast.UnaryExpr:
		x, err := scope.Interpret(e.X)
		if err != nil {
			return nil, err
		}
		return ComputeUnaryOp(x, e.Op)

	case *ast.ArrayType:
		typ, err := scope.Interpret(e.Elt)
		if err != nil {
			return nil, err
		}
		arrType := reflect.SliceOf(typ.(reflect.Type))
		return arrType, nil

	case *ast.MapType:
		keyType, err := scope.Interpret(e.Key)
		if err != nil {
			return nil, err
		}
		valType, err := scope.Interpret(e.Value)
		if err != nil {
			return nil, err
		}
		mapType := reflect.MapOf(keyType.(reflect.Type), valType.(reflect.Type))
		return mapType, nil

	case *ast.ChanType:
		typeI, err := scope.Interpret(e.Value)
		if err != nil {
			return nil, err
		}
		typ, isType := typeI.(reflect.Type)
		if !isType {
			return nil, fmt.Errorf("chan needs to be passed a type not %T", typ)
		}
		return reflect.ChanOf(reflect.BothDir, typ), nil

	case *ast.IndexExpr:
		X, err := scope.Interpret(e.X)
		if err != nil {
			return nil, err
		}
		i, err := scope.Interpret(e.Index)
		if err != nil {
			return nil, err
		}
		xVal := reflect.ValueOf(X)
		if reflect.TypeOf(X).Kind() == reflect.Map {
			val := xVal.MapIndex(reflect.ValueOf(i))
			if !val.IsValid() {
				// If not valid key, return the "zero" type. Eg for int 0, string ""
				return reflect.Zero(xVal.Type().Elem()).Interface(), nil
			}
			return val.Interface(), nil
		}

		iVal, isInt := i.(int)
		if !isInt {
			return nil, fmt.Errorf("index has to be an int not %T", i)
		}
		if iVal >= xVal.Len() || iVal < 0 {
			return nil, errors.New("slice index out of range")
		}
		return xVal.Index(iVal).Interface(), nil

	case *ast.SliceExpr:
		low, err := scope.Interpret(e.Low)
		if err != nil {
			return nil, err
		}
		high, err := scope.Interpret(e.High)
		if err != nil {
			return nil, err
		}
		X, err := scope.Interpret(e.X)
		if err != nil {
			return nil, err
		}
		xVal := reflect.ValueOf(X)
		if low == nil {
			low = 0
		}
		if high == nil {
			high = xVal.Len()
		}
		lowVal, isLowInt := low.(int)
		highVal, isHighInt := high.(int)
		if !isLowInt || !isHighInt {
			return nil, fmt.Errorf("slice: indexes have to be an ints not %T and %T", low, high)
		}
		if lowVal < 0 || highVal >= xVal.Len() {
			return nil, errors.New("slice: index out of bounds")
		}
		return xVal.Slice(lowVal, highVal).Interface(), nil

	case *ast.ParenExpr:
		return scope.Interpret(e.X)

	case *ast.ReturnStmt:
		results := make([]interface{}, len(e.Results))
		for i, result := range e.Results {
			out, err := scope.Interpret(result)
			if err != nil {
				return out, err
			}
			results[i] = out
		}

		if len(results) == 0 {
			return nil, nil
		} else if len(results) == 1 {
			return results[0], nil
		}
		return results, nil

	case *ast.AssignStmt:
		define := e.Tok == token.DEFINE
		lhs := make([]string, len(e.Lhs))
		for i, id := range e.Lhs {
			lhsIdent, isIdent := id.(*ast.Ident)
			if !isIdent {
				return nil, fmt.Errorf("%#v assignment is not ident", id)
			}
			lhs[i] = lhsIdent.Name
		}
		rhs := make([]interface{}, len(e.Rhs))
		for i, expr := range e.Rhs {
			val, err := scope.Interpret(expr)
			if err != nil {
				return nil, err
			}
			rhs[i] = val
		}

		if len(rhs) != 1 && len(rhs) != len(lhs) {
			return nil, fmt.Errorf("assignment count mismatch: %d = %d", len(lhs), len(rhs))
		}
		if len(rhs) == 1 && len(lhs) > 1 && reflect.TypeOf(rhs[0]).Kind() == reflect.Slice {
			rhsV := reflect.ValueOf(rhs[0])
			rhsLen := rhsV.Len()
			if rhsLen != len(lhs) {
				return nil, fmt.Errorf("assignment count mismatch: %d = %d", len(lhs), rhsLen)
			}
			for i := 0; i < rhsLen; i++ {
				variable := lhs[i]
				v := scope.Get(variable)
				if v == nil && !define {
					return nil, fmt.Errorf("variable %#v is not defined", variable)
				}
				scope.Set(variable, rhsV.Index(i).Interface())
			}
		} else {
			for i, r := range rhs {
				variable := lhs[i]
				v := scope.Get(variable)
				if v == nil && !define {
					return nil, fmt.Errorf("variable %#v is not defined", variable)
				}
				scope.Set(variable, r)
			}
		}

		if len(rhs) > 1 {
			return rhs, nil
		}
		return rhs[0], nil

	case *ast.ForStmt:
		s := scope.NewChild()
		s.Interpret(e.Init)
		for {
			ok, err := s.Interpret(e.Cond)
			if err != nil {
				return nil, err
			}
			if !ok.(bool) {
				break
			}
			s.Interpret(e.Body)
			s.Interpret(e.Post)
		}
		return nil, nil
	case *ast.RangeStmt:
		s := scope.NewChild()
		ranger, err := s.Interpret(e.X)
		if err != nil {
			return nil, err
		}
		var key, value string
		if e.Key != nil {
			key = e.Key.(*ast.Ident).Name
		}
		if e.Value != nil {
			value = e.Value.(*ast.Ident).Name
		}
		rv := reflect.ValueOf(ranger)
		switch rv.Type().Kind() {
		case reflect.Array, reflect.Slice:
			for i := 0; i < rv.Len(); i++ {
				if len(key) > 0 {
					s.Set(key, i)
				}
				if len(value) > 0 {
					s.Set(value, rv.Index(i).Interface())
				}
				s.Interpret(e.Body)
			}
		case reflect.Map:
			keys := rv.MapKeys()
			for _, keyV := range keys {
				if len(key) > 0 {
					s.Set(key, keyV.Interface())
				}
				if len(value) > 0 {
					s.Set(value, rv.MapIndex(keyV).Interface())
				}
				s.Interpret(e.Body)
			}
		default:
			return nil, fmt.Errorf("ranging on %s is unsupported", rv.Type().Kind().String())
		}
		return nil, nil
	case *ast.ExprStmt:
		return scope.Interpret(e.X)
	case *ast.DeclStmt:
		return scope.Interpret(e.Decl)
	case *ast.GenDecl:
		for _, spec := range e.Specs {
			if _, err := scope.Interpret(spec); err != nil {
				return nil, err
			}
		}
		return nil, nil
	case *ast.ValueSpec:
		typ, err := scope.Interpret(e.Type)
		if err != nil {
			return nil, err
		}
		zero := reflect.Zero(typ.(reflect.Type)).Interface()
		for i, name := range e.Names {
			if len(e.Values) > i {
				v, err := scope.Interpret(e.Values[i])
				if err != nil {
					return nil, err
				}
				scope.Set(name.Name, v)
			} else {
				scope.Set(name.Name, zero)
			}
		}
		return nil, nil
	case *ast.BlockStmt:
		var outFinal interface{}
		for _, stmts := range e.List {
			out, err := scope.Interpret(stmts)
			if err != nil {
				return out, err
			}
			outFinal = out
		}
		return outFinal, nil

	default:
		return nil, fmt.Errorf("unknown node %#v", e)
	}
}

// StringToType returns the reflect.Type corresponding to the type string provided. Ex: StringToType("int")
func StringToType(str string) (reflect.Type, error) {
	builtinTypes := map[string]reflect.Type{
		"bool":       reflect.TypeOf(true),
		"byte":       reflect.TypeOf(byte(0)),
		"rune":       reflect.TypeOf(rune(0)),
		"string":     reflect.TypeOf(""),
		"int":        reflect.TypeOf(int(0)),
		"int8":       reflect.TypeOf(int8(0)),
		"int16":      reflect.TypeOf(int16(0)),
		"int32":      reflect.TypeOf(int32(0)),
		"int64":      reflect.TypeOf(int64(0)),
		"uint":       reflect.TypeOf(uint(0)),
		"uint8":      reflect.TypeOf(uint8(0)),
		"uint16":     reflect.TypeOf(uint16(0)),
		"uint32":     reflect.TypeOf(uint32(0)),
		"uint64":     reflect.TypeOf(uint64(0)),
		"uintptr":    reflect.TypeOf(uintptr(0)),
		"float32":    reflect.TypeOf(float32(0)),
		"float64":    reflect.TypeOf(float64(0)),
		"complex64":  reflect.TypeOf(complex64(0)),
		"complex128": reflect.TypeOf(complex128(0)),
		"error":      reflect.TypeOf(errors.New("")),
	}
	val, present := builtinTypes[str]
	if !present {
		return nil, fmt.Errorf("type %#v is not in table", str)
	}
	return val, nil
}

// ValuesToInterfaces converts a slice of []reflect.Value to []interface{}
func ValuesToInterfaces(vals []reflect.Value) []interface{} {
	inters := make([]interface{}, len(vals))
	for i, val := range vals {
		inters[i] = val.Interface()
	}
	return inters
}
