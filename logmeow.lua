local function _deep_copy(t)
    if type(t) ~= "table" then return t
    end
    local out = {}
    for k, v in pairs(t) do out[k] = _deep_copy(v) end
    return out
end

local function _table_to_string(t)
    if t == nil then return "nil" end
    local out = "{"
    for _, v in ipairs(t) do
        if type(v) == "table" then
            out = out .. _table_to_string(v) .. ", "
        else
            out = out .. string.gsub(tostring(v), "\n", "\\n") .. ", "
        end
    end
    out = out .. "}"
    return out
end

Props = {"succ", "add", "mul", "proj1", "proj2", "input", "print", "eq", "le", "lt", "isnat", "ispair"}

local function _format_term(term, terms_table)
    if #terms_table[term] == 1 then return "_" .. term end
    if terms_table[term][2] == "num" then return tostring(terms_table[term][3]) end
    if terms_table[term][2] == "world" then return "world(" .. terms_table[term][3] .. ", " .. terms_table[term][4] .. ")" end
    assert(terms_table[term][2] == "pair", "_format_term: term is not a pair")
    local pair_term = {term}
    while terms_table[pair_term[#pair_term]][2] == "pair" do
        local t = table.remove(pair_term)
        for i = 3, #terms_table[t] do
            table.insert(pair_term, terms_table[t][i])
        end
    end
    local buff = {}
    for _, t in ipairs(pair_term) do
        table.insert(buff, _format_term(t, terms_table))
    end
    return "[" .. table.concat(buff, ", ") .. "]"
end

local function _format_goals(goals, terms_table, t, ind)
    local out = {}
    for i, g in ipairs(goals) do
        local add = ""
        if i == t then add = "<" end
        local buff = {}
        if g[1] == "or" then
            for j = 2, #g do
                if j - 1 == ind then
                    table.insert(buff, "[" .. _format_goals(g[j], terms_table, 0, 0) .. "]")
                else
                    table.insert(buff, "{" .. _format_goals(g[j], terms_table, 0, 0) .. "}")
                end
            end
            add = add .. table.concat(buff, " or ")
        else
            for j = 3, #g do
                table.insert(buff, _format_term(g[j], terms_table))
            end
            if g[1] == "prop" then table.insert(buff, Props[g[2]]) end
            if g[1] == "cprop" then table.insert(buff, "P" .. g[2]) end
            add = add .. table.concat(buff, " ")
        end
        if i == t then add = add .. ">" end
        table.insert(out, add)
    end
    return table.concat(out, ", ")
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
    {type = "proj1",
     arity = 2,
     argtype = {"pair", "any"}},
    {type = "proj2",
     arity = 2,
     argtype = {"pair", "any"}},
    {type = "input",
     arity = 3,
     argtype = {"world", "num", "world"}},
    {type = "output",
     arity = 3,
     argtype = {"world", "num", "world"}},
    {type = "eq",
     arity = 2,
     argtype = {"any", "any"}},
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

local function _count_vars_new(args, terms_table)
    local ifvar = {}
    local c = 0
    for i, v in ipairs(args) do
        if #terms_table[v] == 1 then
            ifvar[i] = true
            c = c + 1
        end
    end
    return  c, ifvar
end

local function _check_types_new(args, argtype, terms_table)
    if #args < #argtype then return false end
    for i = 1, #argtype do
        if argtype[i] ~= "any" and #terms_table[args[i]] ~= 1 and argtype[i] ~= terms_table[args[i]][2] then return false end
    end
    return true
end

local function _subst_targets(targets, from, to, replace_left)
    if replace_left == nil then replace_left = true end
    assert(type(targets) == "table", "_subst_targets: targets is not a table")
    for _, s in ipairs(targets) do
        if replace_left and s[1] == from then s[1] = to end
        if s[2] == from then s[2] = to end
    end
end

local function _subst_terms_table(terms_table, from, to)
    assert(type(terms_table) == "table", "_subst_terms_table: terms_table is not a table")
    for _, t in pairs(terms_table) do
        if t[2] == "pair" then
            for i = 3, #t do
                if t[i] == from then t[i] = to end
            end
        end
    end
end

local function _subst_props_subst(props, subst)
    assert(type(props) == "table", "_subst_props: props is not a table")
    assert(type(subst) == "table", "_subst_props: subst is not a table")
    if props[1] == "prop" or props[1] == "cprop" then
        for i = 3, #props do
            for _, s in ipairs(subst) do
                if props[i] == s[1] then
                    props[i] = s[2]
                    break
                end
            end
        end
        return
    end
    local start = 1
    if props[1] == "or" then start = 2 end
    for i = start, #props do _subst_props_subst(props[i], subst) end
end

local function _occur(var, term, terms_table)
    assert(#terms_table[var] == 1, "_occur: var is not a variable")
    if #terms_table[term] == 1 then
        return terms_table[var][1] == terms_table[term][1]
    end
    if terms_table[term][2] ~= "pair" then return false end
    for i = 3, #terms_table[term] do
        if _occur(var, terms_table[term][i], terms_table) then return true end
    end
    return false
end

---unify
---@param term1 any
---@param term2 any
---@param terms_table table _deepcopyしてね
---@return boolean
---@return table?
---@return table?
local function _unify(term1, term2, terms_table)
    local subst = {}
    local targets = {{term1, term2}}
    while #targets > 0 do
        local target = table.remove(targets)
        if target[1] == target[2] then goto continue end
        if #terms_table[target[1]] == 1 then
            if _occur(target[1], target[2], terms_table) then return false end
            _subst_targets(targets, target[1], target[2])
            _subst_terms_table(terms_table, target[1], target[2])
            _subst_targets(subst, target[1], target[2], false)
            table.insert(subst, {target[1], target[2]})
            goto continue
        end
        if #terms_table[target[2]] == 1 then
            table.insert(targets, {target[2], target[1]})
            goto continue
        end
        if terms_table[target[1]][2] ~= terms_table[target[2]][2] then return false end
        if terms_table[target[1]][2] == "num" and terms_table[target[1]][3] ~= terms_table[target[2]][3] then 
            return false
        end
        table.insert(targets, {terms_table[target[1]][3], terms_table[target[2]][3]})
        local l, r = 0, 0
        if #terms_table[target[1]] == 4 then
            l = terms_table[target[1]][4]
        else
            l = #terms_table + 1
            table.insert(terms_table, table.move(terms_table[target[1]], 4, #terms_table[target[1]], 3, {l, "pair"}))
        end
        if #terms_table[target[2]] == 4 then
            r = terms_table[target[2]][4]
        else
            r = #terms_table + 1
            table.insert(terms_table, table.move(terms_table[target[2]], 4, #terms_table[target[2]], 3, {r, "pair"}))
        end
        table.insert(targets, {l, r})
        ::continue::
    end
    return true, subst
end

local function handle_input_new(world, to)
    to[2] = "world"
    to[3] = world[3]
    to[4] = world[4]
    if world[3] == "" then to[3] = io.read() end
    if to[3] == "" then to[3] = to[3] .. "\0" end
    local c = string.sub(to[3], 1, utf8.offset(to[3], 2) - 1)
    to[3] = string.sub(to[3], utf8.offset(to[3], 2), -1)
    local _, b = utf8.codes(c)(c, 0)
    return b
end

---builtinの命題たちを計算して正しい代入を返す 第一の出力が
---- -1 -> 引数が十分確定していない
---- 0 -> 正しい代入がない
---- 1 -> 正しい代入がある
---
---TODO: 分解
---@param prop table assert(prop[1] == "prop")
---@param terms_table table _deepcopyしてね
---@return integer
---@return table?
local function calc_subst_of_builtin(prop, terms_table)
    assert(prop[1] == "prop", "calc_subst_of_builtin_new: the type is not prop")
    local argdatas = {}
    local numvar, ifvar = _count_vars_new(table.move(prop, 3, #prop, 1, argdatas), terms_table)
    local propindex = prop[2]
    local propdata = builtins[propindex]
    local arity = propdata.arity
    assert(#argdatas >= arity, "calc_subst_of_builtin_new: insufficient arguments")
    if numvar >= 3 then return -1 end
    if propdata.type == "eq" then
        local r, subst = _unify(argdatas[1], argdatas[2], terms_table)
        if not r then return 0 end
        return 1, subst
    end
    if propdata.type == "input" then
        if not (ifvar[2] and ifvar[3]) then return 0 end
        if argdatas[2] == argdatas[3] then return 0 end
        local b = handle_input_new(terms_table[argdatas[1]], terms_table[argdatas[3]])
        terms_table[argdatas[2]][2] = "num"
        terms_table[argdatas[2]][3] = b
        return 1, {}
    end
    if numvar == 2 then return -1 end
    if not _check_types_new(argdatas, propdata.argtype, terms_table) then return 0 end
    if propdata.type == "output" then
        if not (ifvar[3]) then return 0 end
        local c = utf8.char(terms_table[argdatas[2]][3])
        io.write(c)
        terms_table[argdatas[3]][2] = "world"
        terms_table[argdatas[3]][3] = terms_table[argdatas[1]][3]
        terms_table[argdatas[3]][4] = terms_table[argdatas[1]][4] .. c
        return 1, {}
    end
    if propdata.type == "proj1" then
        if #terms_table[argdatas[1]] == 1 then return -1 end
        local r, subst = _unify(terms_table[argdatas[1]][3], argdatas[2], terms_table)
        if not r then return 0 end
        return 1, subst
    end
    if propdata.type == "proj2" then
        if #terms_table[argdatas[1]] == 1 then return -1 end
        local l = 0
        if #terms_table[argdatas[1]] == 4 then
            l = terms_table[argdatas[1]][4]
        else
            l = #terms_table + 1
            table.insert(terms_table, table.move(terms_table[argdatas[1]], 4, #terms_table[argdatas[1]], 3, {l, "pair"}))
        end
        local r, subst = _unify(l, argdatas[2], terms_table)
        if not r then return 0 end
        return 1, subst
    end
    local args = {}
    for i = 1, arity do if #terms_table[argdatas[i]] ~= 1 then table.insert(args, terms_table[argdatas[i]][3]) end end
    if propdata.type == "prop" then
        if numvar ~= 0 then return -1 end
        if propdata[1](table.unpack(args)) then return 1, {} end
        return 0
    end
    if propdata.type == "calc" and numvar == 0 then
        table.remove(args, 1)
        if propdata[1](table.unpack(args)) == terms_table[argdatas[1]][3] then return 1, {} end
        return 0
    end
    if propdata.type == "calc" and numvar == 1 then
        local varind = 0
        for i = 1, arity do if ifvar[i] then varind = i end end
        local result = propdata[varind](table.unpack(args))
        if not result then return 0 end
        terms_table[argdatas[varind]][2] = "num"
        terms_table[argdatas[varind]][3] = result
        return 1, {}
    end
    return 0
end

local function _subst_composit(to, subst)
    for _, k in ipairs(subst) do
        _subst_targets(to, k[1], k[2], false)
        table.insert(to, {k[1], k[2]})
    end
end

local function _decomposit_or(goals, t, ind)
    local goals_new = _deep_copy(goals)
    local or_args = table.remove(goals_new, t)[ind + 1]
    for _, p in ipairs(or_args) do
        table.insert(goals_new, p)
    end
    return goals_new
end

---@param prog string
local function parser_nyan(prog)
    local initial = prog:gsub( "\\%s*", ""):gsub("にゃ", "1"):gsub("ん", "|"):gsub("ー", "0")
    local lines = {}
    for w in string.gmatch(initial, "[^\n]+") do
        table.insert(lines, w)
    end
    local cprops = {}
    for i, w in ipairs(lines) do
        local stack = {}
        local vars = {}
        local tmpterms = {}
        local acc = {}
        if i == #lines then
            tmpterms = {{1, "world", "", ""}, {2}}
            stack = {1, 2}
        end
        for u in string.gmatch(w, "[01]+") do
            if u == "1" then
                local r = table.remove(stack)
                local l = table.remove(stack)
                if tmpterms[r][2] == "pair" then
                    table.insert(tmpterms[r], 3, l)
                    table.insert(stack, r)
                else
                    table.insert(tmpterms, {#tmpterms + 1, "pair", l, r})
                    table.insert(stack, #tmpterms)
                end
            elseif u == "10" then
                if cprops[i] == nil then
                    cprops[i] = {{"or"}}
                end
                table.insert(cprops[i][1], acc)
                acc = {}
            elseif string.match(u, "^101") then
                local id = tonumber(string.sub(u, 3), 2)
                if not vars[id] then
                    vars[id] = #tmpterms + 1
                    if i == #lines then
                        table.insert(tmpterms, {#tmpterms + 1})
                    else
                        table.insert(tmpterms, {#tmpterms + 1, id})
                    end
                end
                table.insert(stack, vars[id])
            elseif string.match(u, "^1001") then
                local id = tonumber(string.sub(u, 4), 2)
                table.insert(acc, table.move(stack, 1, #stack, 3, {"prop", id}))
                stack = {}
            elseif string.match(u, "^10001") then
                local id = tonumber(string.sub(u, 5), 2)
                table.insert(acc, table.move(stack, 1, #stack, 3, {"cprop", id}))
                stack = {}
            elseif string.match(u, "^11") then
                local num = tonumber(string.sub(u, 4), 2)
                if "1" == string.sub(u, 3, 3) then num = -num end
                table.insert(tmpterms, {#tmpterms + 1, "num", num})
                table.insert(stack, #tmpterms)
            else
                error("parser_nyan: unknown token")
            end
        end
        if cprops[i] == nil then
            cprops[i] = acc
        else
            table.insert(cprops[i][1], acc)
        end
        cprops[i].terms = tmpterms
    end
    local initial_goal = table.remove(cprops)
    local initial_terms = initial_goal.terms
    initial_goal.terms = nil
    return initial_goal, cprops, initial_terms
end

---@param prog string
local function parser_readable(prog)
    local lines = {}
    for l in string.gmatch(prog:gsub(",", " , "):gsub("%[", " [ "):gsub("%]", " ] "), "[^\n]+") do
        local add = {}
        for w in l:gmatch("[^%s]+") do
            table.insert(add, w)
        end
        table.insert(lines, add)
    end
    local cprops = {}
    for i, w in ipairs(lines) do
        local stack = {}
        local vars = {}
        local tmpterms = {}
        local acc = {}
        if i == #lines then
            tmpterms = {{1, "world", "", ""}, {2}}
            stack = {1, 2}
        end
        for _, u in ipairs(w) do
            if u == "," then
                --pass
            elseif u == "[" then
                table.insert(stack, "[")
            elseif u == "]" then
                local t = table.remove(stack)
                table.insert(tmpterms, {#tmpterms + 1, "pair"})
                while t ~= "[" do
                    table.insert(tmpterms[#tmpterms], 3, t)
                    t = table.remove(stack)
                end
                assert(#tmpterms[#tmpterms] >= 4, "parser_readable: length of pair is 1")
                table.insert(stack, #tmpterms)
            elseif u == "or" then
                if cprops[i] == nil then
                    cprops[i] = {{"or"}}
                end
                table.insert(cprops[i][1], acc)
                acc = {}
            elseif string.match(u, "^_[0-9]+") then
                local id = assert(tonumber(string.sub(u, 2)))
                if not vars[id] then
                    vars[id] = #tmpterms + 1
                    if i == #lines then
                        table.insert(tmpterms, {#tmpterms + 1})
                    else
                        table.insert(tmpterms, {#tmpterms + 1, id})
                    end
                end
                table.insert(stack, vars[id])
            elseif string.match(u, "^P[0-9]+") then
                local id = tonumber(string.sub(u, 2))
                table.insert(acc, table.move(stack, 1, #stack, 3, {"cprop", id}))
                stack = {}
            elseif string.match(u, "^%-?[0-9]+") then
                local num = tonumber(string.sub(u, 1))
                table.insert(tmpterms, {#tmpterms + 1, "num", num})
                table.insert(stack, #tmpterms)
            else
                local id = 0
                for j, p in ipairs(Props) do
                    if p == u then
                        id = j
                        break
                    end
                end
                assert(id ~= 0, "parser_readable: unknown token")
                table.insert(acc, table.move(stack, 1, #stack, 3, {"prop", id}))
                stack = {}
            end
        end
        if cprops[i] == nil then
            cprops[i] = acc
        else
            table.insert(cprops[i][1], acc)
        end
        cprops[i].terms = tmpterms
    end
    local initial_goal = table.remove(cprops)
    local initial_terms = initial_goal.terms
    initial_goal.terms = nil
    return initial_goal, cprops, initial_terms
end

local parsers = {parser_nyan, parser_readable}

---ゴールとユーザー定義関係から代入を求める
---- -1 -> 未完成
---- 0 -> 失敗
---- 1 -> 成功
---TODO: 分解
---@param goals table パースしたやつ
---@param cprops table ユーザー定義関係の一覧
---@param terms_table table 項の対応をみる
---@param debug_handler? fun(t, ind, goals, terms_table, dif, flag)
---@return integer
---@return table?
---@return table?
local function calc_subst(goals, cprops, terms_table, debug_handler)
    local dif = {}
    local t = 1
    if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "start") end
    while t <= #goals do
        --print(t, _table_to_string_i(goals), _table_to_string_i(terms_table))
        if goals[t][1] == "prop" then
            if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "prop") end
            local result, subst = calc_subst_of_builtin(goals[t], terms_table)
            if result == -1 then
                t = t + 1
                goto continue
            end
            if result == 0 then
                if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "return_0") end
                return 0
            end
            assert(subst ~= nil, "calc_subst: prop: subst is nil")
            table.remove(goals, t)
            _subst_props_subst(goals, subst)
            _subst_composit(dif, subst)
            if #goals == 0 then
                if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "return_1") end
                return 1, dif, terms_table
            end
            t = 1
        end
        if goals[t][1] == "cprop" then
            if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "cprop") end
            local propdata = _deep_copy(cprops[goals[t][2]])
            local subst = {}
            for i, d in ipairs(propdata.terms) do
                if type(d[2]) == "number" and d[2] <= #goals[t] - 2 then
                    table.insert(subst, {i, goals[t][d[2] + 2]})
                else
                    if type(d[2]) == "number" then
                        table.insert(terms_table, {#terms_table + 1})
                    else
                        table.insert(terms_table, table.move(d, 2, #d, 2, {#terms_table + 1}))
                    end
                    table.insert(subst, {i, #terms_table})
                end
            end
            propdata.terms = nil
            -- print(_table_to_string_i(tmpsubst))
            _subst_props_subst(propdata, subst)
            table.remove(goals, t)
            table.move(propdata, 1, #propdata, #goals + 1, goals)
            t = 1
        end
        if goals[t][1] == "or" then
            if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "or") end
            local result = -1
            local subst
            local terms_table_new = {}
            local ind = 1
            while ind <= (#goals[t] - 1) do
                terms_table_new = _deep_copy(terms_table)
                if debug_handler then debug_handler(t, ind, goals, terms_table, dif, "create_branch") end
                result, subst, _ = calc_subst(_decomposit_or(goals, t, ind), cprops, terms_table_new, debug_handler)
                if result == 0 then
                    table.remove(goals[t], ind)
                    if #goals[t] == 2 then
                        local or_args = table.remove(goals, t)[2]
                        for _, p in ipairs(or_args) do
                            table.insert(goals, p)
                        end
                        t = 1
                        goto continue
                    end
                end
                if result == -1 then ind = ind + 1 end
                if result == 1 then break end
            end
            if result == -1 then
                t = t + 1
                goto continue
            end
            assert(result == 1, "calc_subst: or: result is not 1")
            terms_table = terms_table_new
            table.remove(goals, t)
            _subst_props_subst(goals, subst)
            _subst_composit(dif, subst)
            if #goals == 0 then 
                if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "return_1") end
                return 1, dif, terms_table
            end
            t = 1
        end
        ::continue::
    end
    if debug_handler then debug_handler(t, 0, goals, terms_table, dif, "return_-1") end
    return -1
end

local function main(prog, parse_mode, debug_handler)
    parse_mode = parse_mode or 1
    local initial_goals, cprops, initial_terms = parsers[parse_mode](prog)
    local result, _, result_terms = calc_subst(initial_goals, cprops, initial_terms, debug_handler)
    assert(result == 1, "main: result is not 1")
    assert(result_terms ~= nil, "main: result_terms is nil")
    assert(result_terms[2][2] == "world", "main: terms[2] is not a world")
end

local function _arg_parse(arg)
    local out = {arg[1]}
    for i = 2, #arg do
        local c = arg[i]
        if c:match("^%-[^%-]") then
            for j = 2, c:len() do
                out[c:sub(j, j)] = true
            end
        elseif out.d == true then
            out["d"] = c
        else
            table.insert(out, c)
        end
    end
    return out
end

local arg = _arg_parse{...}
local file = assert(io.open(arg[1], "r"))
local prog = file:read("a")
file:close()

local log = nil
if arg.d then
    if arg.d == true then
        log = assert(io.open(os.date("%Y%m%d%H%M%S") ..".log", "w"))
    else
        log = assert(io.open(arg.d, "w"))
    end
end

local parser_mode = 1
if arg.r then parser_mode = 2 end

local function debug_write(t, ind, goals, terms_table, dif, flag)
    assert(log)
    log:write(flag .. "\n")
    if not string.match(flag, "^return") then log:write(_format_goals(goals, terms_table, t, ind) .. "\n") end
end

if log then
    main(prog, parser_mode, debug_write)
else
    main(prog, parser_mode)
end
if log then log:close() end
