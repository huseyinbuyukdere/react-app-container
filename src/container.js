"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
exports.__esModule = true;
var react_1 = __importDefault(require("react"));
var container_module_css_1 = __importDefault(require("./container.module.css"));
var SideBar_1 = __importDefault(require("./components/SideBar"));
var Header_1 = __importDefault(require("./components/Header"));
var react_router_dom_1 = require("react-router-dom");
var Container = function (props) {
    var history = react_router_dom_1.useHistory();
    var sideBarMenu = props.designConfig && props.designConfig.sideBarMenu
        ? props.designConfig.sideBarMenu
        : [];
    var headerMenu = props.designConfig && props.designConfig.headerMenu
        ? props.designConfig.headerMenu
        : [];
    var configureMenu = function (menu) {
        menu = menu.map(function (item) {
            var itemOnClick = item.onClick;
            item.onClick = function (routeKey) {
                if (itemOnClick)
                    itemOnClick();
                var route;
                if (routeKey && props.routes) {
                    route = props.routes.find(function (route) { return route.key === routeKey; });
                    if (route) {
                        history.push(route.path);
                    }
                    return;
                }
                if (item.routeKey && props.routes) {
                    route = props.routes.find(function (route) { return route.key === item.routeKey; });
                    if (route) {
                        history.push(route.path);
                    }
                }
            };
            if (item.subMenuItemList) {
                configureMenu(item.subMenuItemList);
            }
            return item;
        });
    };
    configureMenu(sideBarMenu);
    configureMenu(headerMenu);
    return (react_1["default"].createElement("div", { className: container_module_css_1["default"].containerLeftMenu },
        react_1["default"].createElement("div", { className: container_module_css_1["default"].header },
            react_1["default"].createElement(Header_1["default"], { menu: headerMenu, pageName: props.selectedRoute && props.selectedRoute.label, leftContent: props.designConfig &&
                    props.designConfig.headerLeftContent, rightContent: props.designConfig &&
                    props.designConfig.headerRightContent })),
        react_1["default"].createElement("div", { className: container_module_css_1["default"].sidebar },
            react_1["default"].createElement(SideBar_1["default"], { headerContent: props.designConfig &&
                    props.designConfig.sideBarHeaderContent, footerContent: props.designConfig &&
                    props.designConfig.sideBarFooterContent, selectedRouteKey: props.selectedRoute && props.selectedRoute.key, menu: sideBarMenu })),
        react_1["default"].createElement("div", { className: container_module_css_1["default"].main }, props.children)));
};
exports["default"] = Container;
