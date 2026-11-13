local middle = {{{{type = "prop", value = 2, args = {{type = "val", value = 1}, {type = "num", value = 2}, {type = "val", value = 2}}}}},
 query = {{type = "cprop", value = 1, args = {{type = "num", value = 1}, {type = "val", value = 1}}}}}
Props = {"succ", "add", "mul", "proj1", "proj2", "input", "print", "eq", "le", "lt", "isnat", "ispair"}
-- 
--  

local function _deep_copy(t)
    if type(t) ~= "table" then return t
    end
    local out = {}
    for k, v in pairs(t) do out[k] = _deep_copy(v) end
    return out
end

---`from` から `to` に `var` を `args` から引用・適用してコピー `index`は実際は別の変数のトラック用
---@param from table
---@param args table
---@param to table
---@param index number
local function apply_args(from, args, to, index)
    for k, v in pairs(from) do
        if type(v) == "table" then
            to[k] = {}
            if v.type == "val" and args[v.value] then
                to[k].type = args[v.value].type
                to[k].value = _deep_copy(args[v.value].value)
                to[k].index = args[v.value].index
            elseif v.type == "val" then
                to[k].type = v.type
                to[k].value = v.value
                to[k].index = index
            else
                apply_args(v, args, to[k], index)
            end
        else
            to[k] = v
        end
    end
end

local function _table_to_string(t)
    local out = "{"
    for k, v in pairs(t) do
        if type(v) == "table" then
            out = out .. tostring(k) .. " = " .. _table_to_string(v) .. ", "
        else
            out = out .. tostring(k) .. " = ".. tostring(v) .. ", "
        end
    end
    out = out .. "}"
    return out
end

local function reduction(goal, index)
    local to = {}
    if goal.type == "cprop" then
        apply_args(middle[goal.value], goal.args, to, index) --修正案件
    end
    return to
end

local builtins = {
    {type = "calc",
     arity = 2,
     argtype = {"num", "num"},
     (function (x) return (x - 1) end),
     (function (x) return (x + 1) end)},
    {type = "calc",
     arity = 3,
     argtype = {"num", "num", "num"},
     (function (y, z) return (z - y) end),
     (function (x, z) return (z - x) end),
     (function (x, y) return (x + y) end)},
    {type = "calc",
     arity = 3,
     argtype = {"num", "num", "num"},
     (function (y, z) if z % y ~= 0 then return else return math.floor(z/y) end end),
     (function (x, z) if z % x ~= 0 then return else return math.floor(z/x) end end),
     (function (x, y) return x * y end)},
    {type = "calc",
     arity = 2,
     argtype = {"pair", "any"},
     [2] = (function (x) return _deep_copy(x[1]) end),
     flag = "proj"},
    {type = "calc",
     arity = 2,
     argtype = {"pair", "any"},
     [2] = (function (x) return _deep_copy(x[2]) end),
     flag = "proj"},
    {type = "input",
     arity = 3,
     argtype = {"world", "num", "world"}},
    {type = "output",
     arity = 3,
     argtype = {"world", "num", "world"}},
    {type = "calc",
     arity = 2,
     argtype = {"any", "any"},
     (function (x) return _deep_copy(x) end),
     (function (x) return _deep_copy(x) end),
     flag = "eq"},
    {type = "prop",
     arity = 2,
     argtype = {"num", "num"},
     function (x, y) return x <= y end},
    {type = "prop",
     arity = 2,
     argtype = {"num", "num"},
     function (x, y) return x < y end},
    {type = "prop",
     arity = 1,
     argtype = {"num"},
     function (x) return true end},
    {type = "prop",
     arity = 1,
     argtype = {"pair"},
     function (x) return true end}
}

local function _table_eq(a, b)
    if type(a) ~= type(b) then return false end
    if type(a) ~= "table" then return a == b end
    for k, v in pairs(a) do
        if not _table_eq(v, b[k]) then return false end
    end
    for k, _ in pairs(b) do
        if a[k] == nil then return false end
    end
    return true
end

local function _check_types(args, argtype)
    if #args < #argtype then return false end
    for i = 1, #argtype do
        if argtype[i] ~= "any" and args[i].type ~= "val" and argtype[i] ~= args[i].type then return false end
    end
    return true
end

local function _count_vals(args)
    local ifval = {}
    local c = 0
    for i, v in ipairs(args) do
        if v.type == "val" then
            ifval[i] = true
            c = c + 1
        end
    end
    return  c, ifval
end

local function _unicode_read()
    local out = io.read(1)
    local b = string.byte(out)
    if b < 128 then
        -- pass
    elseif b < 0xe0 then
        out =  out .. io.read(1)
    elseif b < 0xf0 then
        out = out .. io.read(2)
    else 
        out =  out .. io.read(3)
    end
    if out ~= "\n" then _ = io.read(1) end -- \n読み取り避け
    return out
end

---builtinの命題たちを計算して正しい代入を返す 第一の出力が
---- -2 -> エラー
---- -1 -> 引数が十分確定していない
---- 0 -> 正しい代入がない
---- 1 -> 正しい代入がある
---TODO: 分解
---@param prop table assert(prop.type == "prop")
---@param numval number
---@param ifval table
---@return integer
---@return string|table
local function calc_builtin_subst(prop, numval, ifval)
    -- assert(prop.type == "prop")
    local subst = {}
    local propindex = prop.value
    local propdata = builtins[propindex]
    local arity = propdata.arity
    if #prop.args < arity then return -2, "insufficient args" end
    if numval >= 3 then return -1, {} end
    if numval == 2 and propdata.type ~= "input" and propdata.flag ~= "eq" then return -1, {} end
    if numval == 2 and propdata.flag == "eq" then return 1, {[prop.args[2].value] = {[prop.args[2].index] = prop.arg[1]}} end
    if not _check_types(prop.args, propdata.argtype) then return 0, {} end
    if numval == 0 then
        if propdata.type == "input" or propdata.type == "output" then return 0, {} end
        local args = {}
        for i = 1, arity do table.insert(args, prop.args[i].value) end
        if propdata.type == "calc" then
            table.remove(args, 2)
            if _table_eq(propdata[2](table.unpack(args)), prop.args[2].value) then return 1, {} end
            return 0, {}
        else 
            if propdata[1](table.unpack(args)) then return 1, {} end
            return 0, {}
        end
    end
    if numval == 1 then
        if propdata.type == "input" then return 0, {} end
        if propdata.type == "output" then
            if ifval[3] then
                io.write(utf8.char(prop.args[2].value))
                return 1, {[prop.args[3].value] = {[prop.args[3].index] = prop.args[1]}}
            end
            return 0, {}
        end
        if propdata.type == "prop" then return -1, {} end
        -- assert(propdata.type == "calc")
        local valind = 0
        for i = 1, arity do if ifval[i] then valind = i end end
        local args = {}
        for i = 1, arity do if i ~= valind then table.insert(args, prop.args[i].value) end end
        if propdata[valind] then
            local result = propdata[valind](table.unpack(args))
            local out = {}
            if not result then return 0, {} end
            if propdata.argtype[valind] == "any" then
                if propdata.flag == "eq" then
                    out = {[prop.args[valind].value] = {[prop.args[valind].index] = {type = prop.args[3 - valind].type, value = result}}}
                else
                    out= {[prop.args[valind].value] = {[prop.args[valind].index] = result}}
                end
            else
                out = {[prop.args[valind].value] = {[prop.args[valind].index] = {type = propdata.argtype[valind], value = result}}}
            end
            return 1, out
        end
        return -1, {}
    end
    -- assert(propdata.type == "input")
    if not (ifval[2] and ifval[3]) then return 0, {} end
    if prop.args[2].index == prop.args[3].index and prop.args[2].value == prop.args[3].value then return 0, {} end
    local c = _unicode_read()
    local _, b = utf8.codes(c)(c, 0)
    local out = {}
    out[prop.args[2].value] = {}
    out[prop.args[3].value] = {}
    out[prop.args[2].value][prop.args[2].index] = {type = "num", value = b}
    out[prop.args[3].value][prop.args[3].index] = prop.args[1]
    return 1, out
end

local function apply_subst(from, subst, to)
    for k, v in pairs(from) do
        if type(v) == "table" then
            to[k] = {}
            if v.type == "val" and (subst[v.value] or {})[v.index] then
                to[k].type = subst[v.value][v.index].type
                to[k].value = _deep_copy(subst[v.value][v.index].value)
                to[k].index = subst[v.value][v.index].index
            elseif v.type == "val" then
                to[k].type = v.type
                to[k].value = v.value
                to[k].index = v.index
            else
                apply_subst(v, subst, to[k])
            end
        else
            to[k] = v
        end
        
    end
end

local prop = {type = "prop", value = 2, args = {{type = "num", value = 3}, {type = "num", value = 4}, {type = "val", value = 1, index = 0}}}
local c, ifval = _count_vals(prop.args)
local result, subst = calc_builtin_subst(prop, c, ifval)
local a = {type = "cprop", value = 1, args = {{type = "pair", value = {{type = "val", value = 1, index = 0}, {type = "num", value = 10}}}, {type = "val", value = 2, index = 0}}}
local to = {}
if result == 1 then
    apply_subst(a, {}, to)
end
print(result, _table_to_string(to))
