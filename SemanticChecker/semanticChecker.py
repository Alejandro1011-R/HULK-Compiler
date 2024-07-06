from AST.ast import *
import cmp.visitor as visitor
from cmp.semantic import Scope
from cmp.semantic import SemanticError
from cmp.semantic import Attribute

#Error messages
WRONG_SIGNATURE = 'Method "%s" already defined in "%s" with a different signature.'
SELF_IS_READONLY = 'Variable "self" is read-only.'
LOCAL_ALREADY_DEFINED = 'Variable "%s" is already defined in method "%s".'
INCOMPATIBLE_TYPES = 'Cannot convert "%s" into "%s".'
VARIABLE_NOT_DEFINED = 'Variable "%s" is not defined in "%s".'
INVALID_OPERATION = 'Operation is not defined between "%s" and "%s".'



class TypeCollector(object):
    def __init__(self, errors=[]):
        self.context = None
        self.errors = errors
    
    @visitor.on('node')
    def visit(self, node):
        pass
    @visitor.when(ProgramNode)
    def visit(self, node: ProgramNode):
        self.context = Context()
        self.context.create_type("Object")
        self.context.create_type("Void")
        self.context.create_type("Number")
        self.context.create_type("Boolean")
        self.context.create_type("String")
        self.context.create_type("Function")
        for decl in node.decl_list:
            self.visit(decl)
        return self.context    
    @visitor.when(TypeDeclNode)
    def visit(self, node: TypeDeclNode):
        try :
            self.context.create_type(node.id)
        except SemanticError as e:
            self.errors.append(e)
    @visitor.when(ProtDeclNode)
    def visit(self, node:ProtDeclNode):
        try :
            
            self.context.create_type(node.id)
        except SemanticError as e:
            self.errors.append(e)





class TypeBuilder:
    def __init__(self, context: Context, errors=[]):
        self.context = context
        self.current_type: Type = None
        self.errors = errors
    
    @visitor.on('node')
    def visit(self, node):
        pass
    @visitor.when(ProgramNode)
    def visit(self, node: ProgramNode):
        for decl in node.decl_list:
            try:
                self.visit(decl)
            except SemanticError as error:
                self.errors.append(error)
    @visitor.when(TypeDeclNode)
    def visit(self, node: TypeDeclNode):
        self.current_type = self.context.get_type(node.id)
        self.current_type.set_parent(self.context.get_type(node.parent) if node.parent != None else self.context.get_type("Object"))
        for feature in node.features:
            self.visit(feature)
    
    @visitor.when(AssignNode)
    def visit(self, node: AssignNode):
        type_node = self.context.get_type(node.var.type) if node.var.type!=None else "Object"
        self.current_type.define_attribute(node.var.id,type_node)
    
    @visitor.when(MethodNode)
    def visit(self, node: MethodNode):
        type=self.context.get_type(node.return_type if node.return_type!=None else 'Object')
        param_names = []
        param_types = []
        for param in node.args:
            aux:VarDefNode=param
            param_names.append(aux.id)
            param_types.append(self.context.get_type(aux.type if aux.type != None else "Object"))
        self.current_type.define_method(node.id,param_names,param_types, type)
    
    @visitor.when(ProtDeclNode)
    def visit(self, node: ProtDeclNode):
        self.current_type= self.context.get_type(node.id)
        self.current_type.set_parent(node.parents if node.parents!=None else "Object")
        for method in node.methods:
            self.visit(method)
    @visitor.when(ProtMethodNode)
    def visit(self, node: ProtMethodNode):
        type=self.context.get_type(node.return_type if node.return_type!=None else 'Object')
        param_names = []
        param_types = []
        for param in node.args:
            aux:VarDefNode=param
            param_names.append(aux.id)
            param_types.append(self.context.get_type(aux.type if aux.type != None else "Object"))
        self.current_type.define_method(node.id,param_names,param_types,type)
    
    @visitor.when(FuncDeclNode)
    def visit(self, node: FuncDeclNode):
        #las funciones seran metodos de tipo "Function"
        function_type : Type =self.context.get_type('Function')
        return_type=self.context.get_type(node.return_type if node.return_type!=None else 'Object')
        param_names = []
        param_types = []
        for param in node.args:
            aux:VarDefNode=param
            param_names.append(aux.id)
            param_types.append(self.context.get_type(aux.type if aux.type != None else "Object"))
        function_type.define_method(node.id,param_names,param_types,return_type)
            


class TypeChecker:
    def __init__(self, context: Context, errors=[]):
        self.context = context
        self.current_type: Type = None
        self.current_method = None
        self.errors:list = errors

    @visitor.on('node')
    def visit(self, node, scope):
        pass

    @visitor.when(ProgramNode)
    def visit(self, node: ProgramNode, scope=None):
        newScope=Scope()
        for decl in node.decl_list:
            self.visit(decl,newScope)
   
    @visitor.when(TypeDeclNode)
    def visit(self, node: TypeDeclNode, scope:Scope):
        self.current_type=self.context.get_type(node.id)
        
        childScope=scope.create_child()
        
        for feature in node.features:
            self.visit(feature,childScope)
    
    @visitor.when(AssignNode)
    def visit(self, node: AssignNode, scope:Scope):
        if scope.is_local(node.var.id):
            print(f'Variable {node.var.id} ya definidia')
            raise
        expr_type:Type=self.visit(node.expr,scope)
        isnt_none=node.var.type!=None
        
        if(isnt_none):
            type:Type=self.context.get_type(node.var.type)
            if(type.name!=expr_type.name):
                self.errors.append(SemanticError(INCOMPATIBLE_TYPES%(type.name,expr_type.name))) 
                raise
        scope.define_variable(node.var.id,expr_type)
        
    @visitor.when(MethodNode)
    def visit(self, node: MethodNode, scope:Scope):
        actual_method:Method=self.current_type.get_method(node.id)
        new_child=scope.create_child()
        
        #Declarando como variables los parametros de la funcion en el 
        #nuevo scope
        for i in range(0,len(actual_method.param_names)):
            new_child.define_variable(actual_method.param_names[i],
                                      actual_method.param_types[i])
        expr_type= self.visit(node.body,new_child)
        if(not node.return_type.conforms_to(expr_type)):
            print(f'Problema con los tipos en metodo "{actual_method.name}"')
            self.errors.append(f'Problema con los tipos en metodo "{actual_method.name}"')
    
    @visitor.when(ExprBlockNode)
    def visit(self, node: ExprBlockNode, scope:Scope):
        expr_return_type=self.context.get_type('Object')
        for expr in node.expr_list:
            expr_return_type=self.visit(expr,scope)
        return expr_return_type
    
    @visitor.when(LetNode)
    def visit(self, node: LetNode, scope:Scope):
        new_scope=scope.create_child()
        for assign in node.assign_list:
            self.visit(assign,new_scope)
        type_expr=self.visit(node.expr,new_scope)
        return type_expr
    
    
    @visitor.when(WhileNode)
    def visit(self, node: WhileNode, scope:Scope):
        expr_type:Type=self.visit(node.cond,scope)
        if(not self.context.get_type('Boolean').conforms_to(expr_type)):
            print(f'Tiene que haber una expresion booleana')
            self.errors.append(f'Tiene que haber una expresion booleana')
        new_scope=scope.create_child()
        while_block_type= self.visit(node.body,new_scope)
        return while_block_type
    
    @visitor.when(ForNode)
    def visit(self, node: ForNode, scope:Scope):
        
        #!faltan cosas cruciales
        
        #magia con la expresion para ver si iterable 
        new_scope=scope.create_child()
        new_scope.define_variable(node.id)
        
        return self.visit(node.body,new_scope)
    
    @visitor.when(DestrAssign)
    def visit(self, node: DestrAssign, scope:Scope):
        
        #? Puede ser el valor nuevo, de distinto tipo
        #? al que se inicio la variable
        
        if not scope.is_defined(node.id):
            self.errors.append(VARIABLE_NOT_DEFINED)
            raise
        
        return self.visit(node.expr,scope)
    
    @visitor.when(MethodCallNode)
    def visit(self, node: MethodCallNode, scope:Scope):
        if not scope.is_defined(node.obj):
            self.errors.append(VARIABLE_NOT_DEFINED)
            raise
        object_instance=scope.find_variable(node.obj)
        actual_method:Method=object_instance.type.get_method(node.id)
        args_types:list[Type]=[]
        for arg in node.args:
            actual_type=self.visit(arg,scope)
            args_types.append(actual_type)
        real_params_types:list[Type]=actual_method.param_types
        if(len(real_params_types)!=len(args_types)):
            self.errors.append(f'Cantidad de argumanetos erronea')
            raise
        for i in range(len(real_params_types)):
            if not real_params_types[i].conforms_to(args_types[i]):
                self.errors.append(f'Tipo de argumento erroneo')
                raise
        return actual_method.return_type
    
    @visitor.when(AttrrCallNode)
    def visit(self ,node : AttrrCallNode, scope:Scope):
        obj_instance=scope.find_variable(node.obj)
        instance_type:Type =obj_instance.type
        atrribute_in_type:Attribute =instance_type.get_attribute(node.id)
        return atrribute_in_type.type
        
        
    
    @visitor.when(FuncCallNode)
    def visit(self ,node : FuncCallNode, scope:Scope):
        
        #tipo donde guardo las funciones globales
        function_type:Type =self.context.get_type('Function')
        actual_function:Method =function_type.get_method(node.id)
        args_types:list[Type]=[]
        for arg in node.args:
            actual_type=self.visit(arg,scope)
            args_types.append(actual_type)
        real_params_types:list[Type]=actual_function.param_types
        if(len(real_params_types)!=len(args_types)):
            self.errors.append(f'Cantidad de argumanetos erronea')
            raise
        for i in range(len(real_params_types)):
            if not real_params_types[i].conforms_to(args_types[i]):
                self.errors.append(f'Tipo de argumento erroneo')
                raise
        return actual_function.return_type
    
    @visitor.when(InstantiateNode)
    def visit(self ,node : InstantiateNode, scope:Scope):
        
        #?Como se saben los argumentos qe debe recibir un tipo
        
        type:Type=self.context.get_type(node.type)
        arg_types=[]
        args_types:list[Type]=[]
        for arg in node.expr_list:
            actual_type=self.visit(arg,scope)
            args_types.append(actual_type)
        