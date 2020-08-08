/// <reference types="react" />
export interface ContainerRoute {
    path: string;
    key: string;
    label: string;
    component: any;
    exact?: boolean;
}
export interface MenuItem {
    label?: string;
    routeKey?: string;
    iconName?: 'api' | 'apps' | 'code' | 'dashboard' | 'expand_less' | 'expand_more' | 'home' | 'info' | 'language' | 'list' | 'mail' | 'mediation' | 'message' | 'perm_idenity' | 'post_add' | 'radio_button_checked' | 'room' | 'settings';
    iconComp?: any;
    customComp?: any;
    onClick?: (routeKey?: string, path?: string) => void;
    subMenuItemList?: MenuItem[];
}
export interface DesignConfig {
    headerMenu?: MenuItem[];
    sideBarMenu?: MenuItem[];
    sideBarHeaderContent?: React.ReactElement | string;
    sideBarFooterContent?: React.ReactElement | string;
    headerLeftContent?: React.ReactElement | string;
    headerRightContent?: React.ReactElement | string;
}
