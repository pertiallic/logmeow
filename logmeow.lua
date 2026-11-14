Props = {"succ", "add", "mul", "proj1", "proj2", "input", "print", "eq", "le", "lt", "isnat", "ispair"}

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
            if v.type == "var" and args[v.value] then
                to[k].type = args[v.value].type
                to[k].value = _deep_copy(args[v.value].value)
                to[k].index = args[v.value].index
            elseif v.type == "var" then
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
    if t == nil then return "nil" end
    local out = "{"
    for k, v in pairs(t) do
        if type(v) == "table" then
            out = out .. tostring(k) .. " = " .. _table_to_string(v) .. ", "
        else
            out = out .. tostring(k) .. " = ".. string.gsub(tostring(v), "\n", "\\n") .. ", "
        end
    end
    out = out .. "}"
    return out
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
        if argtype[i] ~= "any" and args[i].type ~= "var" and argtype[i] ~= args[i].type then return false end
    end
    return true
end

local function _count_vars(args)
    local ifvar = {}
    local c = 0
    for i, v in ipairs(args) do
        if v.type == "var" then
            ifvar[i] = true
            c = c + 1
        end
    end
    return  c, ifvar
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
---@param numvar number
---@param ifvar table
---@return integer
---@return string|table
local function calc_builtin_subst(prop, numvar, ifvar)
    -- assert(prop.type == "prop")
    local propindex = prop.value
    local propdata = builtins[propindex]
    local arity = propdata.arity
    if #prop.args < arity then return -2, "insufficient args" end
    if numvar >= 3 then return -1, {} end
    if numvar == 2 and propdata.type ~= "input" and propdata.flag ~= "eq" then return -1, {} end
    if numvar == 2 and propdata.flag == "eq" then return 1, {[prop.args[2].value] = {[prop.args[2].index] = prop.arg[1]}} end
    if not _check_types(prop.args, propdata.argtype) then return 0, {} end
    if numvar == 0 then
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
    if numvar == 1 then
        if propdata.type == "input" then return 0, {} end
        if propdata.type == "output" then
            if ifvar[3] then
                io.write(utf8.char(prop.args[2].value))
                local result = prop.args[1]
                if debug then
                    result = _deep_copy(prop.args[1])
                    result.value = result.value .. utf8.char(prop.args[2].value)
                end
                return 1, {[prop.args[3].value] = {[prop.args[3].index] = result}}
            end
            return 0, {}
        end
        if propdata.type == "prop" then return -1, {} end
        -- assert(propdata.type == "calc")
        local varind = 0
        for i = 1, arity do if ifvar[i] then varind = i end end
        local args = {}
        for i = 1, arity do if i ~= varind then table.insert(args, prop.args[i].value) end end
        if propdata[varind] then
            local result = propdata[varind](table.unpack(args))
            local out = {}
            if not result then return 0, {} end
            if propdata.argtype[varind] == "any" then
                if propdata.flag == "eq" then
                    out = {[prop.args[varind].value] = {[prop.args[varind].index] = {type = prop.args[3 - varind].type, value = result}}}
                else
                    out= {[prop.args[varind].value] = {[prop.args[varind].index] = result}}
                end
            else
                out = {[prop.args[varind].value] = {[prop.args[varind].index] = {type = propdata.argtype[varind], value = result}}}
            end
            return 1, out
        end
        return -1, {}
    end
    -- assert(propdata.type == "input")
    if not (ifvar[2] and ifvar[3]) then return 0, {} end
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

local function _apply_subst(from, subst, to)
    for k, v in pairs(from) do
        if type(v) == "table" then
            to[k] = {}
            if v.type == "var" and (subst[v.value] or {})[v.index] then
                to[k].type = subst[v.value][v.index].type
                to[k].value = _deep_copy(subst[v.value][v.index].value)
                to[k].index = subst[v.value][v.index].index
            elseif v.type == "var" then
                to[k].type = v.type
                to[k].value = v.value
                to[k].index = v.index
            else
                _apply_subst(v, subst, to[k])
            end
        else
            to[k] = v
        end
    end
end

local function _apply_subst_self(subst, to)
    local tmp = _deep_copy(to)
    for k, v in pairs(tmp) do
        if type(v) == "table" then
            to[k] = {}
            if v.type == "var" and (subst[v.value] or {})[v.index] then
                to[k].type = subst[v.value][v.index].type
                to[k].value = _deep_copy(subst[v.value][v.index].value)
                to[k].index = subst[v.value][v.index].index
            elseif v.type == "var" then
                to[k].type = v.type
                to[k].value = v.value
                to[k].index = v.index
            else
                _apply_subst(v, subst, to[k])
            end
        else
            to[k] = v
        end
    end
end

local function _subst_merge(from, to)
    for var, k in pairs(from) do
        for ind, v in pairs(k) do
            if not to[var] then
                to[var] = {}
            end
            to[var][ind] = v 
        end
    end
end

local function _snapshot_to_string(snap)
    if snap.type == "world" then
        return "world(" .. string.gsub(snap.value, "\n", "\\n") .. ")"
    end
    if snap.type == "var" then
        return "_(" .. snap.value .. "," .. snap.index .. ")"
    end
    if snap.type == "num" then
        return tostring(snap.value)
    end
    if snap.type == "pair" then
        return _snapshot_to_string(snap.value[1]) .. " " ..  _snapshot_to_string(snap.value[2]) .. " pair"
    end
    local out = ""
    if snap.type == "or" then
        for i, v in ipairs(snap.value) do
            if i == snap.done then
                out = out .. "[" 
            else
                out = out .. "{"
            end
            for _, w in ipairs(v) do
                out = out .. _snapshot_to_string(w) .. " "
            end
            if i == snap.done then
                out = out .. "], " 
            else
                out = out .. "}, "
            end
        end
        return out
    end
    if snap.type == "prop" then
        for i, v in ipairs(snap.args) do
            out = out .. _snapshot_to_string(v) .. " "
        end
        return out .. Props[snap.value]
    end
    if snap.type == "cprop" then
        for i, v in ipairs(snap.args) do
            out = out .. _snapshot_to_string(v) .. " "
        end
        return out .. "P(" .. snap.value .. ")"
    end
    for i, v in ipairs(snap) do
        for j, w in ipairs(v) do
            out = out .. _snapshot_to_string(w) .. " "
        end
        out = out .. "ret=" .. tostring(v.ret) .. ", substdif=" .. _table_to_string(v.substdif) .. "\\\n"
    end
    return out
end

local function _print_debug_info(t, snapshots, tag)
    print(tag)
    print("t:", t)
    print(_snapshot_to_string(snapshots))
end

---パースしたデータ構造からプログラムを実行する
---TODO: 分解
---@param middle table パースしたやつ
---@param debug? boolean デバッグモード
---@return table subst 結果的な代入 失敗したら`{}`
local function run(middle, debug) 
    debug = debug or false
    local snapshots = {middle.query}
    local t = 1
    local index = 1
    local failed = false

    while #snapshots ~= 0 and #(snapshots[#snapshots]) >= t do
        if debug then _print_debug_info(t, snapshots, "start") end
        local propdata = snapshots[#snapshots][t]
        if propdata.type == "cprop" then
            local add = {}
            apply_args(middle[propdata.value], propdata.args, add, index)
            index = index + 1
            table.move(add, 1, #add, #(snapshots[#snapshots]) + 1, snapshots[#snapshots])
            table.remove(snapshots[#snapshots], t)
            propdata = snapshots[#snapshots][t]
        end
        if debug then _print_debug_info(t, snapshots, "cprop") end
        if propdata.type == "prop" then
            local c, ifvar = _count_vars(propdata.args)
            local result, tmpsubst = calc_builtin_subst(propdata, c, ifvar)
            if ((tmpsubst[1] or {})[0] or {}).type ~= nil and ((tmpsubst[1] or {})[0] or {}).type ~= "world" then error("world型の変数にworld型ではない数値が代入されました") end
            if result == -2 or type(tmpsubst) == "string" then error("エラー: " .. tmpsubst) end
            if result == -1 then
                t = t + 1
                goto continue1
            end
            if result == 0 then
                if #snapshots == 0 then return {} end
                t = snapshots[#snapshots].ret
                failed = true
                table.remove(snapshots)
                propdata = snapshots[#snapshots][t]
                goto continue1
            end
            table.remove(snapshots[#snapshots], t)
            t = 1
            propdata = snapshots[#snapshots][t]
            _apply_subst_self(tmpsubst, snapshots[#snapshots])
            _subst_merge(tmpsubst, snapshots[#snapshots].substdif)
            ::continue1::
        end
        if debug then _print_debug_info(t, snapshots, "\nprop") end
        if #snapshots == 0 then return {} end
        while #(snapshots[#snapshots]) == 0 do
            if #snapshots == 1 then return snapshots[1].substdif end
            t = snapshots[#snapshots].ret
            _apply_subst_self(snapshots[#snapshots].substdif, snapshots[#snapshots-1])
            _subst_merge(snapshots[#snapshots].substdif, snapshots[#snapshots-1].substdif)
            table.remove(snapshots)
            table.remove(snapshots[#snapshots], t)
            t = 1
            propdata = snapshots[#snapshots][t]
        end
        if debug then _print_debug_info(t, snapshots, "elim") end
        if propdata.type == "or" then
            if failed then
                propdata.done = propdata.done + 1
                failed = false
                if propdata.done > #propdata.value then
                    t = snapshots[#snapshots].ret
                    failed = true
                    table.remove(snapshots)
                end
                goto continue2
            end
            table.insert(snapshots, _deep_copy(snapshots[#snapshots]))
            snapshots[#snapshots].ret = t
            snapshots[#snapshots].substdif = {}
            local newprops = _deep_copy(propdata.value[propdata.done])
            table.move(newprops, 1, #newprops, #(snapshots[#snapshots]) + 1, snapshots[#snapshots])
            table.remove(snapshots[#snapshots], t)
            t = 1
            ::continue2::
        end
        if debug then _print_debug_info(t, snapshots, "or") end
    end
    return {}
end

local middle = {
    {{type = "or",
    value = {{
    {type = "prop", value = 7, args = {{type = "var", value = 1}, {type = "var", value = 3}, {type = "var", value = 2}}}
    },{
    {type = "prop", value = 4, args = {{type = "var", value = 3}, {type = "var", value = 4}}},
    {type = "prop", value = 5, args = {{type = "var", value = 3}, {type = "var", value = 5}}},
    {type = "prop", value = 7, args = {{type = "var", value = 1}, {type = "var", value = 4}, {type = "var", value = 6}}},
    {type = "cprop", value = 1, args = {{type = "var", value = 6}, {type = "var", value = 2}, {type = "var", value = 5}}}
    }},
    done = 1}},
 query = {
    {type = "cprop", value = 1, args = {{type = "world", value = ""}, {type = "var", value = 1, index = 0},
        {type = "pair", value =
        {{type = "num", value = 78},
          {type = "pair", value =
        {{type = "num", value = 121},
          {type = "pair", value =
        {{type = "num", value = 97},
          {type = "pair", value =
        {{type = "num", value = 110},
         {type = "num", value = 10}
        }}}}}}}}}},
    substdif = {}}}

local debug = true
local result = run(middle, debug)
if debug then print(_table_to_string(result)) end
if result[1] == nil then print("execution failed") end