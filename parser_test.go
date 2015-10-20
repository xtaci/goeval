package goeval

import (
	"fmt"
	"testing"
)

func TestExecute(t *testing.T) {
	s := NewScope()
	s.Set("print", fmt.Println)
	s.Eval(`count := 0`)
	s.Eval(`for i:=0;i<100;i=i+1 { 
			count=count+i
		}`)
	s.Eval(`print(count)`)
}
