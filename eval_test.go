package goeval

import (
	"fmt"
	"testing"
)

func TestExecute(t *testing.T) {
	s := NewScope()
	s.Set("print", fmt.Println)
	t.Log(s.Eval(`count := 0`))
	t.Log(s.Eval(`for i:=0;i<100;i=i+1 { 
			count=count+i
		}`))
	t.Log(s.Eval(`print(count)`))
}
